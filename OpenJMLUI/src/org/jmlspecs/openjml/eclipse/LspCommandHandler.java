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
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.jface.dialogs.MessageDialog;
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

    // -----------------------------------------------------------------------
    // Main execute flow
    // -----------------------------------------------------------------------

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        // 1. Resolve targets from the current selection / active editor.
        IEditorPart editor = HandlerUtil.getActiveEditor(event);
        List<SelectionResolver.Target> targets = SelectionResolver.resolve(
                HandlerUtil.getCurrentSelection(event), editor);

        if (targets.isEmpty()) {
            Console.log("" + lspCommand + ": no target files found.");
            return null;
        }

        // 2. Nature gate: warn if any project lacks the OpenJML nature.
        Set<IProject> missing = new LinkedHashSet<>();
        for (SelectionResolver.Target t : targets) {
            IProject proj = owningProject(t);
            if (!JmlNature.hasNature(proj)) missing.add(proj);
        }
        if (!missing.isEmpty()) {
            String names = missing.stream()
                    .map(IProject::getName)
                    .collect(Collectors.joining(", "));
            MessageDialog dialog = new MessageDialog(
                    Display.getDefault().getActiveShell(),
                    "OpenJML — No JML Nature",
                    null,
                    "Project(s) '" + names + "' do not have the OpenJML nature.\n\n"
                    + "Add it now to enable OpenJML checking for these projects.",
                    MessageDialog.WARNING,
                    new String[] { "Add JML Nature", "Cancel" },
                    0 /* default: Add JML Nature */);
            if (dialog.open() != 0) return null; // Cancel
            for (IProject p : missing) JmlNature.enable(p);
        }

        // 3. Group by project, topo-sort, dispatch.
        Map<IProject, List<SelectionResolver.Target>> byProject = new LinkedHashMap<>();
        for (SelectionResolver.Target t : targets) {
            byProject.computeIfAbsent(owningProject(t), k -> new ArrayList<>()).add(t);
        }
        List<IProject> sortedProjects = topoSortProjects(byProject.keySet());

        // Log summary.
        StringBuilder sb = new StringBuilder(lspCommand).append(": ");
        boolean first = true;
        for (IProject proj : sortedProjects) {
            for (SelectionResolver.Target t : byProject.get(proj)) {
                if (!first) sb.append(", ");
                first = false;
                sb.append(switch (t) {
                    case SelectionResolver.Target.File   f -> f.file().getName();
                    case SelectionResolver.Target.Dir    d -> d.container().getName() + "/";
                    case SelectionResolver.Target.Method m -> m.methodFqn();
                });
            }
        }
        Console.log(sb.toString());

        // Dispatch in dependency order.
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
                    case SelectionResolver.Target.Dir d -> {
                        org.eclipse.core.runtime.IPath loc = d.container().getLocation();
                        if (loc != null) paths.add(loc.toOSString());
                    }
                }
            }
            if (!paths.isEmpty()) {
                ExecuteCommandParams params = buildCommand(paths, ctx);
                if (params != null) dispatchCommand(params, null, proj);
            }
        }
        return null;
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
                    if (!sent)
                        Console.log("ERROR: server not connected — command not sent");
                }
              }).exceptionally(t -> {
                boolean sent = sendViaWrapper(
                        org.jmlspecs.openjml.eclipse.LspPartListener.cachedWrapper, params);
                if (!sent)
                    Console.log("ERROR: server not connected — command not sent");
                return null;
              });
        } catch (Throwable t) {
            Console.log("dispatchCommand exception: " + t);
        }
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
                    specsPath     != null ? specsPath     : "",
                    propertiesFile != null ? propertiesFile : "",
                    outputDir     != null ? outputDir     : "");
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

        Map<String, Integer>    inDegree = new LinkedHashMap<>();
        Map<String, Set<String>> rdeps   = new LinkedHashMap<>();
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
    // Concrete handlers registered via plugin.xml
    // -----------------------------------------------------------------------

    /**
     * Runs {@code openjml.checkJML} (JML type-check) on selected files/directories.
     */
    public static final class CheckJML extends LspCommandHandler {
        public CheckJML() { super("openjml.checkJML"); }

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
        public RunRac() { super("openjml.runRac"); }

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
     * <p>When a method is selected (e.g. in the Outline) dispatches
     * {@code openjml.runEscForMethod} with the method FQN.
     */
    public static final class RunEsc extends LspCommandHandler {
        public RunEsc() { super("openjml.runEsc"); }

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
            return new ExecuteCommandParams("openjml.runEscForMethod", args);
        }
    }

    /**
     * Runs {@code openjml.runEscForMethod} on the method under the cursor in
     * the active editor.  Always operates on the active editor — view selections
     * are ignored.
     */
    public static final class RunEscForMethod extends LspCommandHandler {
        public RunEscForMethod() { super("openjml.runEscForMethod"); }

        @Override
        public Object execute(ExecutionEvent event) throws ExecutionException {
            IEditorPart editor = HandlerUtil.getActiveEditor(event);
            if (editor == null) return null;
            if (!(editor.getEditorInput() instanceof IFileEditorInput fi)) return null;
            IFile file = fi.getFile();

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
                    new ExecuteCommandParams("openjml.runEscForMethod", args);
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
        private static final String LSP4E_MARKER = "org.eclipse.lsp4e.diagnostic";
        private static final String SERVER_ID    = "org.jmlspecs.openjml.lsp.server";

        @Override
        public Object execute(ExecutionEvent event) {
            try {
                org.eclipse.core.resources.IWorkspaceRoot root =
                        org.eclipse.core.resources.ResourcesPlugin.getWorkspace().getRoot();
                org.eclipse.core.resources.IMarker[] markers =
                        root.findMarkers(LSP4E_MARKER,
                                /*includeSubtypes=*/ false,
                                org.eclipse.core.resources.IResource.DEPTH_INFINITE);
                int deleted = 0;
                for (org.eclipse.core.resources.IMarker m : markers) {
                    if (SERVER_ID.equals(m.getAttribute("languageServerId"))) {
                        m.delete();
                        deleted++;
                    }
                }
                Console.log("Cleared " + deleted + " OpenJML marker(s).");
            } catch (org.eclipse.core.runtime.CoreException e) {
                Console.log("ClearMarkers failed: " + e);
            }
            return null;
        }
    }

    /**
     * Clears all cached state (Eclipse markers, server index, AST cache) and
     * reindexes the workspace.
     */
    public static final class ClearAndReindex extends LspCommandHandler {
        private static final String LSP4E_MARKER = "org.eclipse.lsp4e.diagnostic";
        private static final String SERVER_ID    = "org.jmlspecs.openjml.lsp.server";

        public ClearAndReindex() { super("openjml.clearAndReindex"); }

        @Override
        public Object execute(ExecutionEvent event) {
            Console.errorlog(lspCommand);

            // 1. Clear all OpenJML Eclipse markers workspace-wide.
            try {
                org.eclipse.core.resources.IWorkspaceRoot root =
                        org.eclipse.core.resources.ResourcesPlugin.getWorkspace().getRoot();
                org.eclipse.core.resources.IMarker[] markers =
                        root.findMarkers(LSP4E_MARKER,
                                /*includeSubtypes=*/ false,
                                org.eclipse.core.resources.IResource.DEPTH_INFINITE);
                int deleted = 0;
                for (org.eclipse.core.resources.IMarker m : markers) {
                    if (SERVER_ID.equals(m.getAttribute("languageServerId"))) {
                        m.delete();
                        deleted++;
                    }
                }
                Console.log("Cleared " + deleted + " marker(s).");
            } catch (org.eclipse.core.runtime.CoreException e) {
                Console.log("Warning: could not clear markers: " + e.getMessage());
            }

            // 2. Send clearAndReindex to the server.
            ExecuteCommandParams p = new ExecuteCommandParams("openjml.clearAndReindex", List.of());
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
}
