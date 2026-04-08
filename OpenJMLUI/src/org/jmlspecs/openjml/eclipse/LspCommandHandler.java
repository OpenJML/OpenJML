/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.lsp4j.services.LanguageServer;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.handlers.HandlerUtil;


/**
 * Eclipse command handler that forwards an LSP {@code workspace/executeCommand}
 * request to the running OpenJML language server.
 *
 * <p>Subclasses (static inner classes) supply the LSP command name and build
 * the {@link ExecuteCommandParams} for the two target categories:
 * <ul>
 *   <li>Path targets (files <em>and</em> directories) — both reduce to an OS
 *       path string and are batched per project into a single command via
 *       {@link #buildCommand}.</li>
 *   <li>Method targets — dispatched individually via {@link #buildMethodCommand}.</li>
 * </ul>
 *
 * <p>All commands use a unified 4-element prefix:
 * <pre>
 *   args[0]  sourcePath     (per-project JDT source folders + dependency sources)
 *   args[1]  classPath      (per-project JDT dependency output dirs + user pref)
 *   args[2]  specsPath      (global OpenJML specs path preference)
 *   args[3]  propertiesFile (fresh generated properties file from tool-option prefs)
 * </pre>
 * Command-specific arguments follow at position 4+.
 *
 * <p>Targets are grouped by owning Eclipse project, projects are sorted in
 * dependency order (so a dependency is processed before the projects that
 * depend on it), and path targets within each project are batched into a
 * single command call.
 */
public abstract class LspCommandHandler extends AbstractHandler {

    protected final String lspCommand;

    protected LspCommandHandler(String lspCommand) {
        this.lspCommand = lspCommand;
    }

    /**
     * Default execute: resolve targets and dispatch grouped by project.
     * Handlers that need pre-dispatch logic (e.g. dirty-file checks) override this.
     */
    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        List<SelectionResolver.Target> targets = SelectionResolver.resolve(
                HandlerUtil.getCurrentSelection(event), HandlerUtil.getActiveEditor(event));
        dispatchGroupedByProject(targets, event);
        return null;
    }

    // -----------------------------------------------------------------------
    // Per-project dispatch infrastructure
    // -----------------------------------------------------------------------

    /**
     * Nature gate: checks that every involved project has the OpenJML nature.
     * Shows a dialog offering to add the nature; returns {@code false} if the
     * user cancels.  Must be called on the UI thread.
     */
    private static boolean ensureNature(List<SelectionResolver.Target> targets) {
        Set<IProject> missing = new LinkedHashSet<>();
        for (SelectionResolver.Target t : targets) {
            IProject proj = owningProject(t);
            if (!JmlNature.hasNature(proj)) missing.add(proj);
        }
        if (missing.isEmpty()) return true;
        String names = missing.stream().map(IProject::getName).collect(Collectors.joining(", "));
        MessageDialog dialog = new MessageDialog(
                Display.getDefault().getActiveShell(),
                "OpenJML — No JML Nature", null,
                "Project(s) '" + names + "' do not have the OpenJML nature.\n\n"
                + "Add it now to enable OpenJML checking for these projects.",
                MessageDialog.WARNING,
                new String[] { "Add JML Nature", "Cancel" }, 0);
        if (dialog.open() != 0) return false;
        for (IProject p : missing) JmlNature.enable(p);
        return true;
    }

    /** Log the selected targets at the start of a dispatch. */
    private static void logTargets(String command, List<SelectionResolver.Target> targets) {
        StringBuilder sb = new StringBuilder(command).append(": ");
        for (int i = 0; i < targets.size(); i++) {
            if (i > 0) sb.append(", ");
            switch (targets.get(i)) {
                case SelectionResolver.Target.File f   -> sb.append("file ").append(f.file().getName());
                case SelectionResolver.Target.Method m -> sb.append("method ").append(m.methodFqn());
                case SelectionResolver.Target.Dir d    -> sb.append("dir ").append(d.container().getName());
            }
        }
        Console.log(sb.toString());
    }

    /**
     * Group targets by Eclipse project, topo-sort projects, and dispatch one
     * command per project via {@link #buildCommand} / {@link #buildMethodCommand}.
     *
     * <p>Does NOT perform a dirty-file check — callers that need one do it
     * before invoking this method.
     */
    protected void dispatchGroupedByProject(
            List<SelectionResolver.Target> targets, ExecutionEvent event) {
        if (targets.isEmpty()) {
            Console.log(lspCommand + ": no target files found.");
            return;
        }
        if (!ensureNature(targets)) return;
        logTargets(lspCommand, targets);

        Map<IProject, List<SelectionResolver.Target>> byProject = new LinkedHashMap<>();
        for (SelectionResolver.Target t : targets) {
            byProject.computeIfAbsent(owningProject(t), k -> new ArrayList<>()).add(t);
        }
        List<IProject> sortedProjects = topoSortProjects(byProject.keySet());

        for (IProject proj : sortedProjects) {
            InvocationContext ctx = resolveInvocationContext(proj);
            List<String> paths = new ArrayList<>();
            for (SelectionResolver.Target t : byProject.get(proj)) {
                switch (t) {
                    case SelectionResolver.Target.Method m ->
                        dispatchMethodTarget(m, ctx);
                    case SelectionResolver.Target.File f -> {
                        org.eclipse.core.runtime.IPath loc = f.file().getLocation();
                        if (loc != null) paths.add(loc.toOSString());
                    }
                    case SelectionResolver.Target.Dir d ->
                        paths.addAll(containerSourcePaths(d.container()));
                }
            }
            if (!paths.isEmpty()) {
                ExecuteCommandParams params = buildCommand(paths, ctx);
                if (params != null) dispatchCommand(params, null, proj);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Override points for subclasses
    // -----------------------------------------------------------------------

    /**
     * Build the {@link ExecuteCommandParams} for one or more OS path targets
     * (files and/or directories) belonging to the same project.
     *
     * <p>All paths are in one call so the server can pass them all to
     * {@code --dirs} in a single tool invocation.
     *
     * @param osPaths  one or more OS file-system paths (files or directories)
     * @param ctx      per-project paths and settings context
     * @return params to dispatch, or {@code null} to skip
     */
    protected ExecuteCommandParams buildCommand(List<String> osPaths, InvocationContext ctx) {
        return null; // default: no path-based dispatch
    }

    /**
     * Build the {@link ExecuteCommandParams} for a method-level target.
     *
     * <p>Default returns {@code null} (no method support).  Subclasses that
     * support per-method dispatch (e.g. {@link RunEsc}) override this.
     *
     * @param uri  document URI of the containing file
     * @param fqn  fully-qualified method name, e.g. {@code com.example.Foo.bar}
     * @param ctx  per-project paths and settings context
     */
    protected ExecuteCommandParams buildMethodCommand(String uri, String fqn,
                                                      InvocationContext ctx) {
        return null; // default: expand method to whole-file path dispatch
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Returns the Eclipse project that owns {@code target}. */
    private static IProject owningProject(SelectionResolver.Target t) {
        return switch (t) {
            case SelectionResolver.Target.File   f -> f.file().getProject();
            case SelectionResolver.Target.Method m -> m.file().getProject();
            case SelectionResolver.Target.Dir    d -> d.container().getProject();
        };
    }

    /**
     * Returns the OS paths to pass to {@code --dirs} for a {@link SelectionResolver.Target.Dir}.
     *
     * <p>When the container is an {@link IProject}, the project's declared Java source folders
     * (CPE_SOURCE entries from its build path) are returned so that openjml does not receive the
     * project root (which includes output folders, config files, etc.).  For any other container
     * (an IFolder, e.g. a package or source directory), the container's own location is returned.
     */
    private static List<String> containerSourcePaths(IContainer container) {
        if (container instanceof IProject project) {
            try {
                IJavaProject jp = JavaCore.create(project);
                if (jp != null && jp.exists()) {
                    List<String> paths = new ArrayList<>();
                    for (IClasspathEntry entry : jp.getRawClasspath()) {
                        if (entry.getEntryKind() == IClasspathEntry.CPE_SOURCE) {
                            org.eclipse.core.runtime.IPath loc =
                                    ResourcesPlugin.getWorkspace().getRoot()
                                            .getFolder(entry.getPath()).getLocation();
                            if (loc != null) paths.add(loc.toOSString());
                        }
                    }
                    if (!paths.isEmpty()) return paths;
                }
            } catch (Exception ignored) {}
        }
        org.eclipse.core.runtime.IPath loc = container.getLocation();
        return loc != null ? List.of(loc.toOSString()) : List.of();
    }

    /** Dispatch a method target, falling back to the file path if no method command is available. */
    private void dispatchMethodTarget(SelectionResolver.Target.Method m, InvocationContext ctx) {
        String uri = m.file().getLocationURI().toString();
        ExecuteCommandParams params = buildMethodCommand(uri, m.methodFqn(), ctx);
        if (params != null) {
            dispatchCommand(params, getDocument(m.file()), m.file().getProject());
        } else {
            // Fall back to whole-file path dispatch.
            org.eclipse.core.runtime.IPath loc = m.file().getLocation();
            if (loc == null) return;
            ExecuteCommandParams fileParams = buildCommand(List.of(loc.toOSString()), ctx);
            if (fileParams != null)
                dispatchCommand(fileParams, getDocument(m.file()), m.file().getProject());
        }
    }

    /**
     * Builds the 4-element fixed-prefix argument list
     * {@code [sourcePath, classPath, specsPath, propertiesFile]} for {@code ctx}.
     */
    protected static List<Object> prefixArgs(InvocationContext ctx) {
        List<Object> args = new ArrayList<>();
        args.add(ctx.sourcePath()     != null ? ctx.sourcePath()     : "");
        args.add(ctx.classPath()      != null ? ctx.classPath()      : "");
        args.add(ctx.specsPath()      != null ? ctx.specsPath()      : "");
        args.add(ctx.propertiesFile() != null ? ctx.propertiesFile() : "");
        return args;
    }

    /** Retrieve the open {@link org.eclipse.jface.text.IDocument} for {@code file}, or {@code null}. */
    private static org.eclipse.jface.text.IDocument getDocument(IFile file) {
        org.eclipse.core.filebuffers.ITextFileBuffer buf =
                org.eclipse.core.filebuffers.FileBuffers.getTextFileBufferManager()
                        .getTextFileBuffer(file.getFullPath(),
                                org.eclipse.core.filebuffers.LocationKind.IFILE);
        return buf != null ? buf.getDocument() : null;
    }

    /**
     * Route {@code params} to the language server.
     * Tries {@code forDocument} then {@code forProject}; falls back to the
     * cached wrapper from {@link LspPartListener}.
     */
    private static void dispatchCommand(ExecuteCommandParams params,
                                        org.eclipse.jface.text.IDocument doc,
                                        org.eclipse.core.resources.IProject project) {
        try {
            java.util.concurrent.CompletableFuture<java.util.Optional<Object>> cf =
                    doc != null
                    ? LanguageServers.forDocument(doc)
                            .computeFirst(s -> s.getWorkspaceService().executeCommand(params))
                    : LanguageServers.forProject(project)
                            .computeFirst(s -> s.getWorkspaceService().executeCommand(params));
            cf.orTimeout(15, java.util.concurrent.TimeUnit.SECONDS)
              .thenAccept(opt -> {
                if (opt == null || opt.isEmpty()) {
                    boolean sent = sendViaWrapper(
                            org.jmlspecs.openjml.eclipse.LspPartListener.cachedWrapper, params);
                    if (!sent) showServerNotConnectedDialog();
                }
              }).exceptionally(t -> {
                boolean sent = sendViaWrapper(
                        org.jmlspecs.openjml.eclipse.LspPartListener.cachedWrapper, params);
                if (!sent) showServerNotConnectedDialog();
                return null;
              });
        } catch (Throwable t) {
            Console.log("dispatchCommand exception: " + t);
        }
    }

    /**
     * Shows a warning dialog telling the user the server is not connected,
     * and offers to restart it.  Safe to call from any thread.
     */
    private static void showServerNotConnectedDialog() {
        Console.errorlog("OpenJML server not connected — command not sent");
        Display display = Display.getDefault();
        if (display == null || display.isDisposed()) return;
        display.asyncExec(() -> {
            String msg =
                    "The OpenJML LSP server is not connected.\n\n"
                    + "The command could not be sent.  Without a running server, all OpenJML\n"
                    + "features (type-checking, ESC, RAC, syntax coloring, etc.) are non-functional.\n\n"
                    + "Click \"Restart\" to restart the server, or \"OK\" to continue without OpenJML.";
            MessageDialog dialog = new MessageDialog(display.getActiveShell(),
                    "OpenJML: Server Not Connected", null, msg,
                    MessageDialog.WARNING,
                    new String[] { "Restart", "OK" }, 0);
            if (dialog.open() == 0) {
                OpenJMLStreamConnectionProvider.triggerReconnect();
            }
        });
    }

    /**
     * Send {@code params} to the language server via the cached
     * {@code LanguageServerWrapper} from {@link LspPartListener} (reflection).
     */
    private static boolean sendViaWrapper(Object wrapper, ExecuteCommandParams params) {
        if (wrapper == null) return false;
        try {
            java.lang.reflect.Method getServer = null;
            for (Class<?> c = wrapper.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
                try {
                    getServer = c.getDeclaredMethod("getServer");
                    getServer.setAccessible(true);
                    break;
                } catch (NoSuchMethodException ignored) {}
            }
            if (getServer == null) return false;
            Object serverFuture = getServer.invoke(wrapper);
            LanguageServer server = null;
            if (serverFuture instanceof java.util.concurrent.CompletableFuture<?> cf) {
                Object result = cf.get(5, java.util.concurrent.TimeUnit.SECONDS);
                if (result instanceof LanguageServer ls) server = ls;
            } else if (serverFuture instanceof LanguageServer ls) {
                server = ls;
            }
            if (server == null) return false;
            server.getWorkspaceService().executeCommand(params);
            return true;
        } catch (Throwable t) {
            Console.log("sendViaWrapper failed: " + t);
            return false;
        }
    }

    // -----------------------------------------------------------------------
    // Per-project invocation context
    // -----------------------------------------------------------------------

    /**
     * All paths and settings needed for a single project's tool invocation.
     *
     * @param sourcePath      project source folders + transitive dep source folders
     * @param classPath       transitive dep output dirs + user classpath pref
     * @param specsPath       global specs path preference
     * @param propertiesFile  freshly written generated properties file (from tool-option prefs)
     * @param outputDir       project JDT output folder (for RAC {@code -d})
     */
    private record InvocationContext(
            String sourcePath,
            String classPath,
            String specsPath,
            String propertiesFile,
            String outputDir) {}

    /**
     * Computes the {@link InvocationContext} for {@code project} using the JDT model
     * and global OpenJML preferences.
     */
    private static InvocationContext resolveInvocationContext(IProject project) {
        try {
            org.eclipse.jdt.core.IJavaProject jp =
                    org.eclipse.jdt.core.JavaCore.create(project);
            if (jp == null || !jp.exists()) return emptyContext();

            List<String> srcParts = new ArrayList<>();
            List<String> cpParts  = new ArrayList<>();
            collectJdtPaths(jp, srcParts, cpParts, new java.util.HashSet<>());

            // Append user-configured classpath preference.
            String prefCp = OpenJMLOptions.value(OpenJMLOptions.classPathKey);
            if (prefCp != null && !prefCp.isBlank()) cpParts.add(prefCp);

            // Project's own JDT output location (for RAC -d).
            String outputDir = null;
            org.eclipse.core.runtime.IPath outPath = jp.getOutputLocation();
            org.eclipse.core.resources.IFolder outFolder =
                    org.eclipse.core.resources.ResourcesPlugin.getWorkspace()
                            .getRoot().getFolder(outPath);
            org.eclipse.core.runtime.IPath outLoc = outFolder.getLocation();
            if (outLoc != null) outputDir = outLoc.toOSString();

            // Global preferences.
            String specsPath      = OpenJMLOptions.value(OpenJMLOptions.specsPathKey);
            String propertiesFile = null;
            java.nio.file.Path pf = OpenJMLOptions.writePropertiesFile();
            if (pf != null) propertiesFile = pf.toString();

            return new InvocationContext(
                    String.join(java.io.File.pathSeparator, srcParts),
                    String.join(java.io.File.pathSeparator, cpParts),
                    specsPath      != null ? specsPath      : "",
                    propertiesFile != null ? propertiesFile : "",
                    outputDir      != null ? outputDir      : "");
        } catch (Exception e) {
            Console.log("resolveInvocationContext failed for " + project.getName() + ": " + e);
            return emptyContext();
        }
    }

    private static InvocationContext emptyContext() {
        return new InvocationContext("", "", "", "", "");
    }

    /**
     * Recursively collects source folders into {@code srcParts} and dependency
     * output directories into {@code cpParts} for {@code jp}.
     */
    private static void collectJdtPaths(
            org.eclipse.jdt.core.IJavaProject jp,
            List<String> srcParts, List<String> cpParts,
            Set<String> visited) throws Exception {

        if (!visited.add(jp.getProject().getName())) return;

        org.eclipse.core.resources.IWorkspaceRoot root =
                org.eclipse.core.resources.ResourcesPlugin.getWorkspace().getRoot();

        // This project's own source folders.
        for (org.eclipse.jdt.core.IPackageFragmentRoot pfr : jp.getPackageFragmentRoots()) {
            if (pfr.getKind() != org.eclipse.jdt.core.IPackageFragmentRoot.K_SOURCE) continue;
            org.eclipse.core.resources.IResource res = pfr.getCorrespondingResource();
            org.eclipse.core.runtime.IPath loc =
                    res != null ? res.getLocation() : pfr.getPath();
            if (loc != null) srcParts.add(loc.toOSString());
        }

        // Walk required projects for output dirs (classpath) and recurse for sources.
        for (org.eclipse.jdt.core.IClasspathEntry entry
                : jp.getResolvedClasspath(/* ignoreUnresolvedEntry= */ true)) {
            if (entry.getEntryKind() != org.eclipse.jdt.core.IClasspathEntry.CPE_PROJECT) continue;
            String depName = entry.getPath().lastSegment();
            org.eclipse.core.resources.IProject depProject = root.getProject(depName);
            org.eclipse.jdt.core.IJavaProject depJp =
                    org.eclipse.jdt.core.JavaCore.create(depProject);
            if (depJp == null || !depJp.exists()) continue;

            // Dependency output location → classpath.
            org.eclipse.core.runtime.IPath outputPath = depJp.getOutputLocation();
            org.eclipse.core.resources.IFolder outputFolder = root.getFolder(outputPath);
            org.eclipse.core.runtime.IPath outputLoc = outputFolder.getLocation();
            if (outputLoc != null) cpParts.add(outputLoc.toOSString());

            // Recurse so transitive dependency sources are included.
            collectJdtPaths(depJp, srcParts, cpParts, visited);
        }
    }

    /**
     * Returns {@code projects} sorted in topological order (dependencies before dependents).
     * Cycles are handled by appending remaining projects in original order.
     */
    private static List<IProject> topoSortProjects(Collection<IProject> projects) {
        Map<String, IProject> byName = new LinkedHashMap<>();
        for (IProject p : projects) byName.put(p.getName(), p);

        Map<String, Integer>     inDegree = new LinkedHashMap<>();
        Map<String, Set<String>> rdeps    = new LinkedHashMap<>();
        for (IProject p : projects) {
            rdeps.put(p.getName(), new LinkedHashSet<>());
            inDegree.put(p.getName(), 0);
        }
        for (IProject p : projects) {
            try {
                org.eclipse.jdt.core.IJavaProject jp =
                        org.eclipse.jdt.core.JavaCore.create(p);
                if (jp == null || !jp.exists()) continue;
                for (String req : jp.getRequiredProjectNames()) {
                    if (!byName.containsKey(req)) continue;
                    rdeps.get(req).add(p.getName());
                    inDegree.merge(p.getName(), 1, Integer::sum);
                }
            } catch (Exception ignored) {}
        }

        Queue<String> queue = new ArrayDeque<>();
        for (Map.Entry<String, Integer> e : inDegree.entrySet()) {
            if (e.getValue() == 0) queue.add(e.getKey());
        }
        List<IProject> result = new ArrayList<>();
        while (!queue.isEmpty()) {
            String name = queue.poll();
            result.add(byName.get(name));
            for (String dependent : rdeps.get(name)) {
                if (inDegree.merge(dependent, -1, Integer::sum) == 0)
                    queue.add(dependent);
            }
        }
        for (IProject p : projects) {
            if (!result.contains(p)) result.add(p);
        }
        return result;
    }

    // -----------------------------------------------------------------------
    // Dirty-file handling for ESC and RAC
    // -----------------------------------------------------------------------

    /** Collect the dirty {@link org.eclipse.core.filebuffers.ITextFileBuffer}s for all targets.
     *  For {@code Dir} targets the full resource subtree is walked. */
    private static List<org.eclipse.core.filebuffers.ITextFileBuffer>
            collectDirtyBuffers(List<SelectionResolver.Target> targets) {
        List<org.eclipse.core.filebuffers.ITextFileBuffer> dirty = new ArrayList<>();
        for (SelectionResolver.Target t : targets) {
            switch (t) {
                case SelectionResolver.Target.File f   -> checkDirtyWithSibling(f.file(), dirty);
                case SelectionResolver.Target.Method m -> checkDirtyWithSibling(m.file(), dirty);
                case SelectionResolver.Target.Dir d    -> {
                    try {
                        d.container().accept(resource -> {
                            if (resource instanceof IFile f
                                    && isSourceFile(f.getName()))
                                checkDirty(f, dirty);
                            return true;  // recurse into sub-folders
                        });
                    } catch (org.eclipse.core.runtime.CoreException ignored) {}
                }
            }
        }
        return dirty;
    }

    private static boolean isSourceFile(String name) {
        return name.endsWith(".java") || name.endsWith(".jml");
    }

    /** Checks {@code file} and its companion (.java↔.jml sibling) for dirtiness. */
    private static void checkDirtyWithSibling(IFile file,
            List<org.eclipse.core.filebuffers.ITextFileBuffer> dirty) {
        checkDirty(file, dirty);
        IFile sibling = siblingSourceFile(file);
        if (sibling != null && sibling.exists()) checkDirty(sibling, dirty);
    }

    /** Returns the .jml sibling of a .java file, or the .java sibling of a .jml file. */
    private static IFile siblingSourceFile(IFile file) {
        String name = file.getName();
        String siblingName;
        if (name.endsWith(".java"))     siblingName = name.substring(0, name.length() - 5) + ".jml";
        else if (name.endsWith(".jml")) siblingName = name.substring(0, name.length() - 4) + ".java";
        else return null;
        org.eclipse.core.resources.IResource member = file.getParent().findMember(siblingName);
        return member instanceof IFile f ? f : null;
    }

    private static void checkDirty(IFile file,
            List<org.eclipse.core.filebuffers.ITextFileBuffer> dirty) {
        if (file == null) return;
        org.eclipse.core.filebuffers.ITextFileBuffer buf =
                org.eclipse.core.filebuffers.FileBuffers.getTextFileBufferManager()
                        .getTextFileBuffer(file.getFullPath(),
                                org.eclipse.core.filebuffers.LocationKind.IFILE);
        if (buf != null && buf.isDirty()) dirty.add(buf);
    }

    /**
     * Check for dirty editors among {@code targets} and, based on the
     * {@link OpenJMLOptions#escDirtyFilesBehaviorKey} preference, either save
     * them, proceed as-is (using in-memory content), or ask the user.
     *
     * <p>Must be called on the UI thread (may open a dialog).
     *
     * @return {@code true} if ESC should proceed, {@code false} if the user cancelled
     */
    static boolean handleDirtyFilesForEsc(List<SelectionResolver.Target> targets) {
        List<org.eclipse.core.filebuffers.ITextFileBuffer> dirtyBuffers = collectDirtyBuffers(targets);
        if (dirtyBuffers.isEmpty()) return true;

        String behavior = OpenJMLOptions.value(OpenJMLOptions.escDirtyFilesBehaviorKey);
        if (behavior == null) behavior = "ask";

        switch (behavior) {
            case "content" -> { return true; }
            case "save"    -> { saveBuffers(dirtyBuffers); return true; }
            default        -> { /* "ask" — fall through to dialog */ }
        }

        // "ask": show MessageDialogWithToggle with custom button labels.
        MessageDialogWithToggle dlg = new MessageDialogWithToggle(
                Display.getDefault().getActiveShell(),
                "OpenJML — Unsaved Changes",
                null,
                dirtyBuffers.size() + " file(s) have unsaved changes:\n"
                + formatDirtyFileList(dirtyBuffers) + "\n"
                + "Choose how ESC should handle the edited content:",
                MessageDialog.QUESTION,
                // NOTE: Eclipse always assigns IDialogConstants.CANCEL_ID (1) to any
                // button labelled "Cancel", regardless of array position.  Keep
                // "Cancel" at index 1 and "Save and Run ESC" at index 2 so there
                // is no collision with the save action.
                new String[] {
                    "Act on Edited Content",
                    IDialogConstants.CANCEL_LABEL,
                    "Save and Run ESC" },
                0,  // default button: "Act on Edited Content"
                "Remember my choice (can be changed in Preferences \u2192 OpenJML)",
                false);
        int result = dlg.open();

        // MessageDialogWithToggle assigns IDialogConstants.INTERNAL_ID (256) to the first
        // non-cancel button, incrementing for each subsequent non-cancel button.
        // Cancel always gets IDialogConstants.CANCEL_ID (1).
        final int ACT_ID  = IDialogConstants.INTERNAL_ID;      // 256
        final int SAVE_ID = IDialogConstants.INTERNAL_ID + 1;  // 257

        // Persist "don't ask again" choice to the preference store.
        if (dlg.getToggleState()) {
            String newBehavior = (result == ACT_ID) ? "content" : (result == SAVE_ID) ? "save" : "ask";
            org.openjml.ui.Activator.getDefault().getPreferenceStore()
                    .setValue(OpenJMLOptions.escDirtyFilesBehaviorKey, newBehavior);
        }

        if (result == ACT_ID)  return true;                        // "Act on Edited Content"
        if (result == SAVE_ID) { saveBuffers(dirtyBuffers); return true; }  // "Save and Run ESC"
        return false;  // Cancel (IDialogConstants.CANCEL_ID = 1) or window closed
    }

    /** Returns a bullet list of filenames for dirty-file dialog messages. */
    private static String formatDirtyFileList(
            List<org.eclipse.core.filebuffers.ITextFileBuffer> buffers) {
        StringBuilder sb = new StringBuilder();
        for (org.eclipse.core.filebuffers.ITextFileBuffer buf : buffers) {
            sb.append("  \u2022 ").append(buf.getLocation().lastSegment()).append("\n");
        }
        return sb.toString();
    }

    private static void saveBuffers(List<org.eclipse.core.filebuffers.ITextFileBuffer> buffers) {
        NullProgressMonitor monitor = new NullProgressMonitor();
        for (org.eclipse.core.filebuffers.ITextFileBuffer buf : buffers) {
            try {
                buf.commit(monitor, false);
            } catch (org.eclipse.core.runtime.CoreException e) {
                Console.log("Warning: could not save buffer: " + e.getMessage());
            }
        }
    }

    /**
     * Check for dirty editors among {@code targets} and, based on the
     * {@link OpenJMLOptions#racSaveBeforeKey} preference, either save them
     * automatically or ask the user.
     *
     * <p>RAC cannot operate on unsaved content.  When dirty files are found:
     * <ul>
     *   <li>If "always save" is set, files are saved silently.</li>
     *   <li>Otherwise a dialog asks to save or cancel.</li>
     * </ul>
     *
     * <p>Must be called on the UI thread (may open a dialog).
     *
     * @return {@code true} if RAC should proceed, {@code false} if the user cancelled
     */
    static boolean handleDirtyFilesForRac(List<SelectionResolver.Target> targets) {
        List<org.eclipse.core.filebuffers.ITextFileBuffer> dirtyBuffers = collectDirtyBuffers(targets);
        if (dirtyBuffers.isEmpty()) return true;

        if (org.openjml.ui.Activator.getDefault().getPreferenceStore()
                .getBoolean(OpenJMLOptions.racSaveBeforeKey)) {
            saveBuffers(dirtyBuffers);
            return true;
        }

        // Ask the user: save or cancel.
        MessageDialogWithToggle dlg = new MessageDialogWithToggle(
                Display.getDefault().getActiveShell(),
                "OpenJML — Unsaved Changes",
                null,
                dirtyBuffers.size() + " file(s) have unsaved changes:\n"
                + formatDirtyFileList(dirtyBuffers) + "\n"
                + "RAC requires saved files. Save and run RAC, or cancel?\n\n"
                + "The Java+RAC compilation will be executed in an Eclipse background job.",
                MessageDialog.QUESTION,
                new String[] { "Save and Run RAC", IDialogConstants.CANCEL_LABEL },
                0,  // default button: "Save and Run RAC"
                "Always save edited files before running RAC (no dialog)",
                false);
        int result = dlg.open();

        if (dlg.getToggleState()) {
            org.openjml.ui.Activator.getDefault().getPreferenceStore()
                    .setValue(OpenJMLOptions.racSaveBeforeKey, true);
        }

        // "Save and Run RAC" gets IDialogConstants.INTERNAL_ID (256); Cancel gets CANCEL_ID (1).
        if (result == IDialogConstants.INTERNAL_ID) { saveBuffers(dirtyBuffers); return true; }
        return false;  // Cancel
    }

    // -----------------------------------------------------------------------
    // Concrete handlers registered via plugin.xml
    // -----------------------------------------------------------------------

    /**
     * Runs {@code openjml.checkJML} (JML type-check) on selected files/directories.
     *
     * <p>No dirty-file dialog is shown: the LSP server automatically uses
     * in-memory (edited) content for {@code --check} via its {@code lastContent}
     * map, so checking on unsaved files works transparently without user
     * interaction.  The equivalent policy for ESC is configurable via
     * {@link OpenJMLOptions#escDirtyFilesBehaviorKey} and enforced in
     * {@link RunEsc} / {@link RunEscForMethod}.
     */
    public static final class CheckJML extends LspCommandHandler {
        public CheckJML() { super(OpenJMLConstants.CMD_CHECK_JML); }

        @Override
        protected ExecuteCommandParams buildCommand(List<String> osPaths, InvocationContext ctx) {
            List<Object> args = prefixArgs(ctx);
            args.addAll(osPaths);
            return new ExecuteCommandParams(lspCommand, args);
        }
    }

    /**
     * Runs {@code openjml.runRac} on the selected files or directories.
     *
     * <p>The per-project JDT output folder is passed as {@code outputDir} so
     * RAC-compiled {@code .class} files land alongside the regular compiled classes.
     */
    public static final class RunRac extends LspCommandHandler {
        public RunRac() { super(OpenJMLConstants.CMD_RUN_RAC); }

        /**
         * Saves dirty files, then runs a JDT build per project (waiting for
         * auto-build if enabled, or triggering an explicit incremental build
         * otherwise) before dispatching the RAC command to the LSP server.
         *
         * <p>The build step runs in a background {@link Job} so the UI thread
         * is not blocked while waiting for compilation to finish.
         */
        @Override
        public Object execute(ExecutionEvent event) throws ExecutionException {
            // 1. Capture targets on the UI thread (selection is live here).
            List<SelectionResolver.Target> targets = SelectionResolver.resolve(
                    HandlerUtil.getCurrentSelection(event), HandlerUtil.getActiveEditor(event));

            // 2. Save dirty files or cancel (UI thread — may open a dialog).
            if (!handleDirtyFilesForRac(targets)) return null;

            // 3. Ensure JML nature on all involved projects (UI thread — may open a dialog).
            if (!ensureNature(targets)) return null;

            // 4. Log and organise targets (UI thread).
            if (targets.isEmpty()) {
                Console.log(lspCommand + ": no target files found.");
                return null;
            }
            logTargets(lspCommand, targets);

            // Group targets by project and topo-sort (mirrors dispatchGroupedByProject).
            Map<IProject, List<SelectionResolver.Target>> byProject = new LinkedHashMap<>();
            for (SelectionResolver.Target t : targets)
                byProject.computeIfAbsent(owningProject(t), k -> new ArrayList<>()).add(t);
            List<IProject> sortedProjects = topoSortProjects(byProject.keySet());

            // Capture a final reference for the lambda.
            final Map<IProject, List<SelectionResolver.Target>> byProjectFinal = byProject;

            // 5. Build then dispatch — in a background Job so the UI thread is free.
            Job job = new Job("OpenJML: Build and Run RAC") {
                @Override
                protected IStatus run(IProgressMonitor monitor) {
                    boolean autoBuilding =
                            ResourcesPlugin.getWorkspace().getDescription().isAutoBuilding();
                    for (IProject proj : sortedProjects) {
                        if (monitor.isCanceled()) return Status.CANCEL_STATUS;

                        // Wait for or trigger a JDT compile before RAC.
                        if (autoBuilding) {
                            try {
                                Job.getJobManager().join(
                                        ResourcesPlugin.FAMILY_AUTO_BUILD, monitor);
                            } catch (OperationCanceledException | InterruptedException ignored) {}
                        } else {
                            try {
                                proj.build(IncrementalProjectBuilder.INCREMENTAL_BUILD, monitor);
                            } catch (CoreException ignored) {}
                        }

                        // Collect OS paths for this project and dispatch RAC.
                        List<String> paths = new ArrayList<>();
                        for (SelectionResolver.Target t : byProjectFinal.get(proj)) {
                            switch (t) {
                                case SelectionResolver.Target.File f -> {
                                    org.eclipse.core.runtime.IPath loc = f.file().getLocation();
                                    if (loc != null) paths.add(loc.toOSString());
                                }
                                case SelectionResolver.Target.Method m -> {
                                    org.eclipse.core.runtime.IPath loc = m.file().getLocation();
                                    if (loc != null) paths.add(loc.toOSString());
                                }
                                case SelectionResolver.Target.Dir d ->
                                    paths.addAll(containerSourcePaths(d.container()));
                                default -> {}
                            }
                        }
                        if (!paths.isEmpty()) {
                            InvocationContext ctx = resolveInvocationContext(proj);
                            ExecuteCommandParams params = buildCommand(paths, ctx);
                            if (params != null) dispatchCommand(params, null, proj);
                        }
                    }
                    return Status.OK_STATUS;
                }
            };
            job.setUser(false);
            job.setSystem(false);
            job.schedule();
            return null;
        }

        @Override
        protected ExecuteCommandParams buildCommand(List<String> osPaths, InvocationContext ctx) {
            List<Object> args = prefixArgs(ctx);
            args.add(ctx.outputDir() != null ? ctx.outputDir() : "");
            args.addAll(osPaths);
            return new ExecuteCommandParams(lspCommand, args);
        }
    }

    /**
     * Runs {@code openjml.runEsc} on the selected entities.
     *
     * <p>When a method is selected (e.g. in the Outline), dispatches
     * {@code openjml.runEscForMethod} with the method FQN so that only
     * that method is checked.
     *
     * <p>File and directory targets are grouped by Eclipse project and dispatched
     * as a single {@code openjml.runEsc} command per project.
     */
    public static final class RunEsc extends LspCommandHandler {
        public RunEsc() { super(OpenJMLConstants.CMD_RUN_ESC); }

        @Override
        public Object execute(ExecutionEvent event) throws ExecutionException {
            // Resolve targets before showing any dialog — the live IEvaluationContext
            // backing HandlerUtil.getActiveEditor(event) may change focus while a
            // modal dialog is open, making a second resolve return empty results.
            List<SelectionResolver.Target> targets = SelectionResolver.resolve(
                    HandlerUtil.getCurrentSelection(event), HandlerUtil.getActiveEditor(event));
            if (!handleDirtyFilesForEsc(targets)) return null;
            dispatchGroupedByProject(targets, event);
            return null;
        }

        @Override
        protected ExecuteCommandParams buildCommand(List<String> osPaths, InvocationContext ctx) {
            List<Object> args = prefixArgs(ctx);
            args.addAll(osPaths);
            return new ExecuteCommandParams(lspCommand, args);
        }

        @Override
        protected ExecuteCommandParams buildMethodCommand(String uri, String fqn,
                                                          InvocationContext ctx) {
            List<Object> args = prefixArgs(ctx);
            args.add(uri);
            args.add(fqn != null ? fqn : "");
            return new ExecuteCommandParams(OpenJMLConstants.CMD_RUN_ESC_FOR_METHOD, args);
        }
    }

    /**
     * Runs {@code openjml.runEscForMethod} on the method under the cursor in
     * the active editor.  Always operates on the active editor — view selections
     * are ignored.
     */
    public static final class RunEscForMethod extends LspCommandHandler {
        public RunEscForMethod() { super(OpenJMLConstants.CMD_RUN_ESC_FOR_METHOD); }

        @Override
        public Object execute(ExecutionEvent event) throws ExecutionException {
            IEditorPart editor = HandlerUtil.getActiveEditor(event);
            if (editor == null) return null;
            if (!(editor.getEditorInput() instanceof IFileEditorInput fi)) return null;
            IFile file = fi.getFile();

            if (!handleDirtyFilesForEsc(List.of(new SelectionResolver.Target.File(file)))) return null;

            if (!JmlNature.hasNature(file.getProject())) {
                MessageDialog dialog = new MessageDialog(
                        Display.getDefault().getActiveShell(),
                        "OpenJML — No JML Nature",
                        null,
                        "Project '" + file.getProject().getName()
                        + "' does not have the OpenJML nature.\n\n"
                        + "Add it now to enable OpenJML checking for this project.",
                        MessageDialog.WARNING,
                        new String[] { "Add JML Nature", "Cancel" },
                        0 /* default: Add JML Nature */);
                if (dialog.open() != 0) return null;
                JmlNature.enable(file.getProject());
            }

            String uri = file.getLocationURI().toString();
            Console.log(lspCommand + " -> " + uri);

            InvocationContext ctx = resolveInvocationContext(file.getProject());
            // TODO: resolve method FQN from cursor position via JDT IMethod.
            // For now send empty FQN; the server ESCs the whole file.
            List<Object> args = prefixArgs(ctx);
            args.add(uri);
            args.add("");
            ExecuteCommandParams params =
                    new ExecuteCommandParams(OpenJMLConstants.CMD_RUN_ESC_FOR_METHOD, args);
            dispatchCommand(params, getDocument(file), file.getProject());
            return null;
        }

        @Override
        protected ExecuteCommandParams buildCommand(List<String> osPaths, InvocationContext ctx) {
            return null; // execute() is fully overridden; this is never called
        }
    }

    /**
     * Deletes all OpenJML diagnostic markers from the entire workspace directly
     * via the Eclipse {@link org.eclipse.core.resources.IMarker} API.
     */
    public static final class ClearMarkers extends AbstractHandler {
        @Override
        public Object execute(ExecutionEvent event) {
            try {
                org.eclipse.core.resources.IWorkspaceRoot root =
                        org.eclipse.core.resources.ResourcesPlugin.getWorkspace().getRoot();
                int deleted = 0;
                for (org.eclipse.core.resources.IMarker m : root.findMarkers(
                        OpenJMLConstants.JML_PROBLEM_MARKER, true,
                        org.eclipse.core.resources.IResource.DEPTH_INFINITE)) {
                    m.delete(); deleted++;
                }
                for (org.eclipse.core.resources.IMarker m : root.findMarkers(
                        OpenJMLConstants.JML_ESC_MARKER, false,
                        org.eclipse.core.resources.IResource.DEPTH_INFINITE)) {
                    m.delete(); deleted++;
                }
                Console.log("Cleared " + deleted + " OpenJML marker(s).");
            } catch (org.eclipse.core.runtime.CoreException e) {
                Console.log("ClearMarkers failed: " + e);
            }
            // Tell the server to clear its internal diagnostic state so that
            // stale diagnostics are not re-published on the next LSP4E event.
            org.eclipse.lsp4j.ExecuteCommandParams p =
                    new org.eclipse.lsp4j.ExecuteCommandParams(
                            OpenJMLConstants.CMD_CLEAR_MARKERS, java.util.List.of());
            for (org.eclipse.core.resources.IProject proj :
                    org.eclipse.core.resources.ResourcesPlugin.getWorkspace()
                            .getRoot().getProjects()) {
                if (proj.isOpen() && JmlNature.hasNature(proj)) {
                    org.eclipse.lsp4e.LanguageServers.forProject(proj)
                            .computeFirst(server ->
                                    server.getWorkspaceService().executeCommand(p));
                    break;  // one server instance handles all projects
                }
            }
            return null;
        }
    }

    /**
     * Clears all cached state (Eclipse markers, server index, AST cache) and
     * reindexes the workspace.
     */
    public static final class ClearAndReindex extends LspCommandHandler {
        public ClearAndReindex() { super(OpenJMLConstants.CMD_CLEAR_AND_REINDEX); }

        @Override
        public Object execute(ExecutionEvent event) {
            Console.log(lspCommand);

            // 1. Clear all OpenJML Eclipse markers workspace-wide.
            try {
                org.eclipse.core.resources.IWorkspaceRoot root =
                        org.eclipse.core.resources.ResourcesPlugin.getWorkspace().getRoot();
                int deleted = 0;
                for (org.eclipse.core.resources.IMarker m : root.findMarkers(
                        OpenJMLConstants.JML_PROBLEM_MARKER, true,
                        org.eclipse.core.resources.IResource.DEPTH_INFINITE)) {
                    m.delete(); deleted++;
                }
                for (org.eclipse.core.resources.IMarker m : root.findMarkers(
                        OpenJMLConstants.JML_ESC_MARKER, false,
                        org.eclipse.core.resources.IResource.DEPTH_INFINITE)) {
                    m.delete(); deleted++;
                }
                Console.log("Cleared " + deleted + " marker(s).");
            } catch (org.eclipse.core.runtime.CoreException e) {
                Console.log("Warning: could not clear markers: " + e.getMessage());
            }

            // 2. Send clearAndReindex to the server.
            ExecuteCommandParams p = new ExecuteCommandParams(OpenJMLConstants.CMD_CLEAR_AND_REINDEX, List.of());
            if (sendViaWrapper(LspPartListener.cachedWrapper, p)) {
                return null;
            }
            for (org.eclipse.core.resources.IProject project :
                    org.eclipse.core.resources.ResourcesPlugin.getWorkspace()
                            .getRoot().getProjects()) {
                if (JmlNature.hasNature(project)) {
                    LanguageServers.forProject(project).computeFirst(
                            server -> server.getWorkspaceService().executeCommand(p));
                    return null;
                }
            }
            Console.log("WARNING: no connected server found — clearAndReindex not sent.");
            return null;
        }

        @Override
        protected ExecuteCommandParams buildCommand(List<String> osPaths, InvocationContext ctx) {
            return null; // execute() is fully overridden; this is never called
        }
    }

    /**
     * Cancels running ESC verification tasks.
     *
     * <p>Queries the server for the live list of running tasks, then shows a
     * modal dialog with checkboxes (one row per task).  Initial check state is
     * derived from the current Eclipse selection.  Three buttons:
     * <ul>
     *   <li><b>Cancel selected</b> — sends {@code openjml.cancelEsc(key)} for
     *       each checked task.</li>
     *   <li><b>Cancel all</b> — sends {@code openjml.cancelEsc} with no argument,
     *       cancelling everything regardless of checkbox state.</li>
     *   <li><b>Don't cancel</b> — dismisses without sending anything.</li>
     * </ul>
     */
    public static final class CancelEsc extends org.eclipse.core.commands.AbstractHandler {

        @Override
        public Object execute(org.eclipse.core.commands.ExecutionEvent event) throws org.eclipse.core.commands.ExecutionException {
            // Resolve current selection now (on the UI thread) for pre-checking.
            Set<String> selectionKeys = resolveSelectionKeys(event);
            IProject project = findJmlProject();

            // Query server on a background thread, then open the dialog.
            Job.create("Query running ESC tasks", monitor -> {
                List<String> tasks = queryRunningTasks(project);
                Display.getDefault().syncExec(
                        () -> showCancelDialog(event, tasks, selectionKeys, project));
                return Status.OK_STATUS;
            }).schedule();
            return null;
        }

        /** Converts the current Eclipse selection into a set of ESC task keys. */
        private static Set<String> resolveSelectionKeys(org.eclipse.core.commands.ExecutionEvent event) {
            List<SelectionResolver.Target> targets = SelectionResolver.resolve(
                    HandlerUtil.getCurrentSelection(event),
                    HandlerUtil.getActiveEditor(event));
            Set<String> keys = new LinkedHashSet<>();
            for (SelectionResolver.Target t : targets) {
                switch (t) {
                    case SelectionResolver.Target.File f -> {
                        java.net.URI u = org.eclipse.lsp4e.LSPEclipseUtils.toUri(f.file());
                        if (u != null) keys.add(u.toString());
                    }
                    case SelectionResolver.Target.Method m -> {
                        java.net.URI u = org.eclipse.lsp4e.LSPEclipseUtils.toUri(m.file());
                        if (u != null) {
                            String fqn = m.methodFqn();
                            String simple = fqn.contains(".")
                                    ? fqn.substring(fqn.lastIndexOf('.') + 1) : fqn;
                            keys.add(u.toString() + "#" + simple);
                        }
                    }
                    default -> {} // Dir targets have no direct task-key match
                }
            }
            return keys;
        }

        /** Queries {@code openjml.getRunningEscTasks} and returns the task-key list. */
        @SuppressWarnings("unchecked")
        private static List<String> queryRunningTasks(IProject project) {
            try {
                // Prefer direct server access (same JVM, fastest path).
                org.jmlspecs.openjml.eclipse.OpenJMLLanguageClient lc =
                        org.jmlspecs.openjml.eclipse.OpenJMLCodeMiningProvider.languageClient;
                LanguageServer ls = lc != null ? lc.server() : null;
                if (ls != null) {
                    Object raw = ls.getWorkspaceService()
                            .executeCommand(new ExecuteCommandParams(
                                    OpenJMLConstants.CMD_GET_RUNNING_ESC_TASKS, List.of()))
                            .get(5, java.util.concurrent.TimeUnit.SECONDS);
                    return toStringList(raw);
                }
                // Fall back to LSP4E routing.
                if (project != null) {
                    Object raw = LanguageServers.forProject(project)
                            .computeFirst(s -> s.getWorkspaceService()
                                    .executeCommand(new ExecuteCommandParams(
                                            OpenJMLConstants.CMD_GET_RUNNING_ESC_TASKS, List.of())))
                            .get(5, java.util.concurrent.TimeUnit.SECONDS)
                            .orElse(null);
                    return toStringList(raw);
                }
            } catch (Throwable t) {
                Console.log("getRunningEscTasks failed: " + t);
            }
            return List.of();
        }

        /** Extracts {@code List<String>} from a Gson-deserialized command result. */
        private static List<String> toStringList(Object raw) {
            if (raw instanceof List<?> list) {
                List<String> result = new ArrayList<>();
                for (Object e : list) result.add(String.valueOf(e));
                return result;
            }
            try {
                if (raw instanceof com.google.gson.JsonArray arr) {
                    List<String> result = new ArrayList<>();
                    for (com.google.gson.JsonElement e : arr) result.add(e.getAsString());
                    return result;
                }
            } catch (NoClassDefFoundError ignored) {}
            return List.of();
        }

        /** Opens the cancel dialog on the UI thread. */
        private static void showCancelDialog(org.eclipse.core.commands.ExecutionEvent event,
                List<String> tasks, Set<String> selectionKeys, IProject project) {
            org.eclipse.swt.widgets.Shell shell = HandlerUtil.getActiveShell(event);
            if (shell == null) shell = Display.getDefault().getActiveShell();

            if (tasks.isEmpty()) {
                new MessageDialog(shell, "Cancel ESC", null,
                        "No ESC verification tasks are currently running.",
                        MessageDialog.INFORMATION, new String[]{"OK"}, 0).open();
                return;
            }

            // Determine initial check state from the current Eclipse selection.
            // Pre-select matching tasks; fall back to all if nothing matches.
            Set<String> preChecked;
            if (!selectionKeys.isEmpty()) {
                preChecked = new LinkedHashSet<>();
                for (String task : tasks) {
                    if (selectionKeys.contains(task)) {
                        preChecked.add(task);
                    } else {
                        // A bare-URI selection key pre-selects matching "uri#method" tasks.
                        for (String sk : selectionKeys) {
                            if (task.startsWith(sk + "#") || task.equals(sk)) {
                                preChecked.add(task);
                                break;
                            }
                        }
                    }
                }
                if (preChecked.isEmpty()) preChecked = new LinkedHashSet<>(tasks);
            } else {
                preChecked = new LinkedHashSet<>(tasks);
            }

            CancelEscDialog dlg = new CancelEscDialog(shell, tasks, preChecked);
            int result = dlg.open();

            if (result == CancelEscDialog.CANCEL_ALL_ID) {
                sendCancelCommand(null, project);
                Console.log("Cancel ESC: cancelled all tasks.");
            } else if (result == IDialogConstants.OK_ID) {
                List<String> checked = dlg.getCheckedTasks();
                for (String key : checked) sendCancelCommand(key, project);
                Console.log("Cancel ESC: cancelled " + checked.size() + " task(s).");
            }
            // IDialogConstants.CANCEL_ID (Don't cancel) — no action.
        }

        /** Sends {@code openjml.cancelEsc} for the given key (null = cancel all). */
        private static void sendCancelCommand(String key, IProject project) {
            List<Object> args = (key != null) ? List.of(key) : List.of();
            ExecuteCommandParams params = new ExecuteCommandParams(
                    OpenJMLConstants.CMD_CANCEL_ESC, args);
            if (!sendViaWrapper(org.jmlspecs.openjml.eclipse.LspPartListener.cachedWrapper, params)) {
                dispatchCommand(params, null, project);
            }
        }
    }

    /** Returns the first open project that has the OpenJML JML nature. */
    private static IProject findJmlProject() {
        for (IProject p : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
            if (p.isOpen() && JmlNature.hasNature(p)) return p;
        }
        return null;
    }

    /**
     * Converts a running-task key to a human-readable label for the cancel dialog.
     * <ul>
     *   <li>{@code "file:///path/Foo.java"} → {@code "Foo.java  (all methods)"}</li>
     *   <li>{@code "file:///path/Foo.java#bar"} → {@code "Foo.java  \u2014 bar"}</li>
     * </ul>
     */
    static String taskLabel(String key) {
        int hash = key.lastIndexOf('#');
        if (hash >= 0) {
            String uriPart = key.substring(0, hash);
            String method  = key.substring(hash + 1);
            int slash = uriPart.lastIndexOf('/');
            String file = slash >= 0 ? uriPart.substring(slash + 1) : uriPart;
            return file + "  \u2014 " + method;
        }
        int slash = key.lastIndexOf('/');
        String file = slash >= 0 ? key.substring(slash + 1) : key;
        return file + "  (all methods)";
    }

    /**
     * Checkbox dialog for selecting which running ESC tasks to cancel.
     *
     * <p>Return codes:
     * <ul>
     *   <li>{@link IDialogConstants#OK_ID} (0) — "Cancel selected" button pressed.</li>
     *   <li>{@link #CANCEL_ALL_ID} — "Cancel all" button pressed.</li>
     *   <li>{@link IDialogConstants#CANCEL_ID} (1) — "Don't cancel" or Escape.</li>
     * </ul>
     */
    private static class CancelEscDialog extends org.eclipse.jface.dialogs.Dialog {

        static final int CANCEL_ALL_ID = IDialogConstants.CLIENT_ID;

        private final List<String> tasks;
        private final Set<String> preChecked;
        private org.eclipse.jface.viewers.CheckboxTableViewer tableViewer;
        private List<String> checkedTasks = List.of();

        CancelEscDialog(org.eclipse.swt.widgets.Shell shell,
                        List<String> tasks, Set<String> preChecked) {
            super(shell);
            this.tasks = tasks;
            this.preChecked = preChecked;
            setShellStyle(getShellStyle() | org.eclipse.swt.SWT.RESIZE);
        }

        @Override
        protected void configureShell(org.eclipse.swt.widgets.Shell newShell) {
            super.configureShell(newShell);
            newShell.setText("Cancel ESC Verification");
        }

        @Override
        protected org.eclipse.swt.widgets.Control createDialogArea(
                org.eclipse.swt.widgets.Composite parent) {
            org.eclipse.swt.widgets.Composite container =
                    (org.eclipse.swt.widgets.Composite) super.createDialogArea(parent);

            org.eclipse.swt.widgets.Label label =
                    new org.eclipse.swt.widgets.Label(container, org.eclipse.swt.SWT.WRAP);
            label.setText("Select the ESC tasks to cancel:");
            label.setLayoutData(new org.eclipse.swt.layout.GridData(
                    org.eclipse.swt.SWT.FILL, org.eclipse.swt.SWT.TOP, true, false));

            tableViewer = org.eclipse.jface.viewers.CheckboxTableViewer.newCheckList(
                    container,
                    org.eclipse.swt.SWT.BORDER | org.eclipse.swt.SWT.V_SCROLL);
            org.eclipse.swt.layout.GridData gd = new org.eclipse.swt.layout.GridData(
                    org.eclipse.swt.SWT.FILL, org.eclipse.swt.SWT.FILL, true, true);
            gd.heightHint = 150;
            gd.widthHint  = 450;
            tableViewer.getTable().setLayoutData(gd);

            tableViewer.setContentProvider(
                    new org.eclipse.jface.viewers.ArrayContentProvider());
            tableViewer.setLabelProvider(
                    new org.eclipse.jface.viewers.LabelProvider() {
                        @Override public String getText(Object element) {
                            return taskLabel((String) element);
                        }
                    });
            tableViewer.setInput(tasks.toArray());
            for (String task : tasks) {
                tableViewer.setChecked(task, preChecked.contains(task));
            }
            return container;
        }

        @Override
        protected void createButtonsForButtonBar(org.eclipse.swt.widgets.Composite parent) {
            createButton(parent, IDialogConstants.OK_ID,     "Cancel selected", true);
            createButton(parent, CANCEL_ALL_ID,              "Cancel all",      false);
            createButton(parent, IDialogConstants.CANCEL_ID, "Don't cancel",    false);
        }

        @Override
        protected void buttonPressed(int buttonId) {
            if (buttonId == IDialogConstants.OK_ID) {
                checkedTasks = java.util.Arrays.stream(tableViewer.getCheckedElements())
                        .map(o -> (String) o)
                        .collect(Collectors.toList());
            }
            super.buttonPressed(buttonId);
        }

        List<String> getCheckedTasks() { return checkedTasks; }
    }
}
