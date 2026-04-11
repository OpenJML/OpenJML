/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;

/**
 * Listens for resource changes in Eclipse and notifies the OpenJML LSP server
 * when project configuration relevant to JML changes on disk.
 *
 * <p>Watched change types:
 * <ul>
 *   <li>{@code .classpath} files modified in JML-natured projects.</li>
 *   <li>Project descriptions changed ({@link IResourceDelta#DESCRIPTION}) — covers
 *       project dependency changes, nature add/remove, and similar structural edits.</li>
 *   <li>{@code openjml.properties} files modified in JML-natured projects.</li>
 * </ul>
 *
 * <p>When such a change is detected, the listener debounces notifications (500 ms)
 * to coalesce rapid bursts (e.g., batch nature additions) into a single dialog.
 * The dialog lets the user choose how to respond:
 * <ul>
 *   <li><b>Re-check all</b> — send updated settings then run {@code --check} on all
 *       JML-project source paths.</li>
 *   <li><b>Re-ESC all</b> — send updated settings then run {@code --esc}.</li>
 *   <li><b>Clear diagnostics</b> — clear markers without re-checking.</li>
 *   <li><b>Do nothing</b> — send updated settings only (keeps new classpath in sync).</li>
 * </ul>
 * The "remember my choice" toggle suppresses future dialogs until the preference is
 * cleared in the OpenJML preference page.
 */
public class OpenJMLResourceChangeListener implements IResourceChangeListener {

    /** Preference key for the remembered config-change action. */
    public static final String PREF_CONFIG_CHANGE_ACTION = "openjml.configChangeAction";

    /** Sentinel value meaning "always show the dialog". */
    private static final String ALWAYS_ASK = "";

    private static final int DEBOUNCE_MS = 500;

    /**
     * JML-relevant parts of a project description.
     * Build-spec changes (JDT builder additions/removals) are intentionally excluded —
     * they do not affect what JML checks would produce.
     */
    private record DescSnapshot(String natures, String refs, String dynRefs) {
        static DescSnapshot of(IProject project) throws org.eclipse.core.runtime.CoreException {
            org.eclipse.core.resources.IProjectDescription d = project.getDescription();
            String[] nat = d.getNatureIds().clone();
            Arrays.sort(nat);
            String[] ref = Arrays.stream(d.getReferencedProjects())
                    .map(IProject::getName).sorted().toArray(String[]::new);
            String[] dyn = Arrays.stream(d.getDynamicReferences())
                    .map(IProject::getName).sorted().toArray(String[]::new);
            return new DescSnapshot(Arrays.toString(nat),
                                    Arrays.toString(ref),
                                    Arrays.toString(dyn));
        }
        boolean relevantlyDifferentFrom(DescSnapshot other) {
            return !natures.equals(other.natures)
                || !refs.equals(other.refs)
                || !dynRefs.equals(other.dynRefs);
        }
        void logDiffFrom(DescSnapshot prev, String projectName) {
            if (!natures.equals(prev.natures))
                System.err.println("[OpenJML] project natures changed for " + projectName
                        + ": " + prev.natures + " -> " + natures);
            if (!refs.equals(prev.refs))
                System.err.println("[OpenJML] project refs changed for " + projectName
                        + ": " + prev.refs + " -> " + refs);
            if (!dynRefs.equals(prev.dynRefs))
                System.err.println("[OpenJML] project dynRefs changed for " + projectName
                        + ": " + prev.dynRefs + " -> " + dynRefs);
        }
    }

    /**
     * Snapshot of each JML-natured project's JML-relevant description parts.
     * Key = project name.  Pre-populated by {@link #initialize} before the listener
     * is registered so that spurious DESCRIPTION events at startup (e.g. JDT updating
     * the build spec during workspace restore) are filtered out.
     */
    private final Map<String, DescSnapshot> descriptionSnapshots = new ConcurrentHashMap<>();

    /**
     * Pre-populate description snapshots for all currently open JML-natured projects.
     * Must be called <em>before</em> registering the listener with the workspace so
     * that spurious DESCRIPTION events at startup are filtered out.
     *
     * @param root the workspace root (from {@code ResourcesPlugin.getWorkspace().getRoot()})
     */
    public void initialize(org.eclipse.core.resources.IWorkspaceRoot root) {
        for (IProject project : root.getProjects()) {
            if (project.isOpen()) {
                try {
                    if (JmlNature.hasNature(project)) {
                        descriptionSnapshots.put(project.getName(), DescSnapshot.of(project));
                    }
                } catch (Exception e) {
                    // ignore: if we can't snapshot, we'll show the dialog on first event
                }
            }
        }
    }

    private final ScheduledExecutorService debouncer =
            Executors.newSingleThreadScheduledExecutor(r -> {
                Thread t = new Thread(r, "openjml-config-debouncer");
                t.setDaemon(true);
                return t;
            });

    /** Accumulated projects awaiting dialog; replaced atomically on each debounce reset. */
    private final AtomicReference<Set<IProject>> pendingProjects =
            new AtomicReference<>(Collections.synchronizedSet(new LinkedHashSet<>()));

    private volatile ScheduledFuture<?> pendingTask;

    @Override
    public void resourceChanged(IResourceChangeEvent event) {
        if (event.getType() != IResourceChangeEvent.POST_CHANGE) return;
        IResourceDelta delta = event.getDelta();
        if (delta == null) return;

        Set<IProject> affected = new LinkedHashSet<>();
        try {
            delta.accept(new IResourceDeltaVisitor() {
                @Override
                public boolean visit(IResourceDelta d) throws CoreException {
                    IResource resource = d.getResource();

                    // Project level: detect description changes (dependencies, natures).
                    // Ignore events that carry OPEN — those are workspace-restore /
                    // project-open events, not real config edits.  Returning false
                    // also prevents descending into the project's children (e.g.
                    // .classpath) so those file-level checks are not triggered either.
                    if (resource.getType() == IResource.PROJECT) {
                        IProject project = (IProject) resource;
                        boolean isOpen = (d.getFlags() & IResourceDelta.OPEN) != 0;
                        if (isOpen) {
                            return false;  // workspace restore — skip children
                        }
                        if (project.isOpen() && JmlNature.hasNature(project)) {
                            boolean descChanged = (d.getFlags() & IResourceDelta.DESCRIPTION) != 0;
                            if (descChanged) {
                                // Only trigger the dialog if something JML-relevant changed
                                // (natures, project references).  Eclipse fires spurious
                                // DESCRIPTION events at startup when JDT updates the build
                                // spec; those changes don't affect what JML checks produce.
                                try {
                                    DescSnapshot current = DescSnapshot.of(project);
                                    DescSnapshot prev = descriptionSnapshots.put(
                                            project.getName(), current);
                                    if (prev == null) {
                                        System.err.println("[OpenJML] new project description: "
                                                + project.getName()
                                                + " natures=" + current.natures());
                                        affected.add(project);
                                    } else if (current.relevantlyDifferentFrom(prev)) {
                                        current.logDiffFrom(prev, project.getName());
                                        affected.add(project);
                                    }
                                } catch (org.eclipse.core.runtime.CoreException e) {
                                    // Can't read description: play it safe and show dialog.
                                    affected.add(project);
                                }
                            }
                        }
                        return true;  // descend into project to find .classpath etc.
                    }

                    // File level: detect .classpath and openjml.properties changes
                    if (resource.getType() == IResource.FILE
                            && (d.getKind() == IResourceDelta.CHANGED
                                || d.getKind() == IResourceDelta.ADDED
                                || d.getKind() == IResourceDelta.REMOVED)) {
                        String name = resource.getName();
                        if (".classpath".equals(name) || "openjml.properties".equals(name)) {
                            IProject project = resource.getProject();
                            if (project != null && project.isOpen()
                                    && JmlNature.hasNature(project)) {
                                System.err.println("[OpenJML] config file changed: " + resource.getFullPath());
                                affected.add(project);
                            }
                        }
                    }
                    return true;
                }
            });
        } catch (CoreException e) {
            Console.log("OpenJMLResourceChangeListener: delta visit error: " + e.getMessage());
        }

        if (!affected.isEmpty()) {
            System.err.println("[OpenJML] config changed, scheduling dialog for: "
                    + affected.stream().map(IProject::getName).collect(java.util.stream.Collectors.joining(", ")));
            pendingProjects.get().addAll(affected);
            scheduleDialog();
        }
    }

    private void scheduleDialog() {
        ScheduledFuture<?> old = pendingTask;
        if (old != null) old.cancel(false);
        pendingTask = debouncer.schedule(() -> {
            Set<IProject> projects = pendingProjects.getAndSet(
                    Collections.synchronizedSet(new LinkedHashSet<>()));
            if (!projects.isEmpty()) {
                Display.getDefault().asyncExec(() -> showConfigChangeDialog(projects));
            }
        }, DEBOUNCE_MS, TimeUnit.MILLISECONDS);
    }

    private void showConfigChangeDialog(Set<IProject> affectedProjects) {
        org.eclipse.jface.preference.IPreferenceStore prefs =
                org.openjml.ui.Activator.getDefault().getPreferenceStore();
        String remembered = prefs.getString(PREF_CONFIG_CHANGE_ACTION);

        if (remembered != null && !remembered.isEmpty()) {
            // User previously chose "remember" — apply the stored action directly.
            applyConfigChangeAction(remembered, affectedProjects);
            return;
        }

        // Build message
        String projectNames;
        if (affectedProjects.size() == 1) {
            projectNames = "project " + affectedProjects.iterator().next().getName();
        } else {
            projectNames = affectedProjects.size() + " projects";
        }
        String message = "OpenJML configuration changed in " + projectNames
                + " (classpath, properties, or dependencies).\n\nWhat would you like to do?";

        String[] buttons = {
            "Re-check all",     // index 0
            "Re-ESC all",       // index 1
            "Clear diagnostics",// index 2
            "Do nothing"        // index 3
        };

        Shell shell = PlatformUI.isWorkbenchRunning()
                ? PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell()
                : null;
        if (shell == null) {
            // No shell available (e.g., headless run) — just update settings.
            applyConfigChangeAction(buttons[3], affectedProjects);
            return;
        }

        MessageDialogWithToggle dialog = new MessageDialogWithToggle(
                shell,
                "OpenJML Configuration Changed",
                null,  // image
                message,
                org.eclipse.jface.dialogs.MessageDialog.QUESTION,
                buttons,
                0,     // default button index
                "Remember my choice",
                false  // initial toggle state
        );

        int result = dialog.open();
        // result is the index of the button pressed (0–3); negative means cancelled/closed
        int buttonIndex = (result >= 0 && result < buttons.length) ? result : 3;
        String choice = buttons[buttonIndex];

        if (dialog.getToggleState()) {
            prefs.setValue(PREF_CONFIG_CHANGE_ACTION, choice);
        }

        applyConfigChangeAction(choice, affectedProjects);
    }

    private void applyConfigChangeAction(String action, Set<IProject> affectedProjects) {
        // Always send updated settings first so server has latest classpath/roots.
        LspPartListener.sendSettingsToServer();

        if ("Re-check all".equals(action)) {
            sendCheckAll(affectedProjects);
        } else if ("Re-ESC all".equals(action)) {
            sendCheckAll(affectedProjects);
            sendEscAll(affectedProjects);
        } else if ("Clear diagnostics".equals(action)) {
            sendClearMarkers(affectedProjects);
        }
        // "Do nothing": settings update already sent above.
    }

    private static void sendCheckAll(Set<IProject> projects) {
        List<String> paths = projects.stream()
                .filter(IProject::isOpen)
                .map(p -> p.getLocation().toOSString())
                .filter(p -> p != null)
                .collect(java.util.stream.Collectors.toList());
        if (paths.isEmpty()) return;
        // Build args: [sourcePath, classPath, specsPath, propertiesFile, path1, ...]
        List<Object> args = new java.util.ArrayList<>();
        args.add(""); args.add(""); args.add(""); args.add("");
        args.addAll(paths);
        ExecuteCommandParams p = new ExecuteCommandParams(OpenJMLConstants.CMD_CHECK_JML, args);
        sendCommandToAnyServer(projects, p);
    }

    private static void sendEscAll(Set<IProject> projects) {
        List<String> paths = projects.stream()
                .filter(IProject::isOpen)
                .map(p -> p.getLocation().toOSString())
                .filter(p -> p != null)
                .collect(java.util.stream.Collectors.toList());
        if (paths.isEmpty()) return;
        List<Object> args = new java.util.ArrayList<>();
        args.add(""); args.add(""); args.add(""); args.add("");
        args.addAll(paths);
        ExecuteCommandParams p = new ExecuteCommandParams(OpenJMLConstants.CMD_RUN_ESC, args);
        sendCommandToAnyServer(projects, p);
    }

    private static void sendClearMarkers(Set<IProject> projects) {
        ExecuteCommandParams p = new ExecuteCommandParams(
                OpenJMLConstants.CMD_CLEAR_MARKERS, List.of());
        sendCommandToAnyServer(projects, p);
    }

    private static void sendCommandToAnyServer(Set<IProject> projects, ExecuteCommandParams p) {
        for (IProject proj : projects) {
            if (proj.isOpen()) {
                org.eclipse.lsp4e.LanguageServers.forProject(proj)
                        .computeFirst(server -> server.getWorkspaceService().executeCommand(p));
                return;  // one server handles all commands
            }
        }
    }

    /** Shuts down the debounce executor. Call from {@code Activator.stop()}. */
    public void dispose() {
        debouncer.shutdownNow();
    }
}
