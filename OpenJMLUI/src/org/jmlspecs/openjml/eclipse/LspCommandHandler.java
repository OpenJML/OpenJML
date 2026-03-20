/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.LinkedHashSet;
import java.util.List;
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
 * <p>Subclasses (static inner classes) supply the LSP command name.
 * They are registered in {@code plugin.xml} via
 * {@code org.eclipse.ui.handlers} extension points.
 *
 * <p>Target resolution: the handler first collects targets from the current
 * workbench selection (Package Explorer, Project Explorer, Outline, etc.),
 * expanding projects and folders recursively.  If the selection is empty it
 * falls back to the file open in the active editor.  Method-level selections
 * (e.g. a method in the Outline) are preserved as {@link SelectionResolver.Target.Method}
 * so that ESC can operate at method granularity.
 *
 * <p>A warning dialog is shown if any involved project lacks the OpenJML nature.
 *
 * <p>Keybindings (defined in plugin.xml):
 * <ul>
 *   <li>{@code Ctrl/Cmd + Shift + J, E} — Run ESC on current file</li>
 *   <li>{@code Ctrl/Cmd + Shift + J, M} — Run ESC for method under cursor</li>
 * </ul>
 */
public abstract class LspCommandHandler extends AbstractHandler {

    protected final String lspCommand;

    protected LspCommandHandler(String lspCommand) {
        this.lspCommand = lspCommand;
    }

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        // 1. Resolve targets from the current selection / active editor.
        IEditorPart editor = HandlerUtil.getActiveEditor(event);
        List<SelectionResolver.Target> targets = SelectionResolver.resolve(
                HandlerUtil.getCurrentSelection(event), editor);

        if (targets.isEmpty()) {
            Console.log("[OpenJML] " + lspCommand + ": no target files found.");
            return null;
        }

        // 2. Nature gate: warn if any project lacks the OpenJML nature.
        Set<IProject> missing = new LinkedHashSet<>();
        for (SelectionResolver.Target t : targets) {
            IProject proj = switch (t) {
                case SelectionResolver.Target.File f   -> f.file().getProject();
                case SelectionResolver.Target.Method m -> m.file().getProject();
                case SelectionResolver.Target.Dir d    -> d.container().getProject();
            };
            if (!JmlNature.hasNature(proj)) missing.add(proj);
        }
        if (!missing.isEmpty()) {
            String names = missing.stream()
                    .map(IProject::getName)
                    .collect(Collectors.joining(", "));
            // execute() runs on the UI thread — open the dialog synchronously so
            // we can add the nature and immediately proceed to dispatch.
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
            // Fall through to dispatch now that natures are added.
        }

        // 3. Log and dispatch a command for each target.
        StringBuilder sb = new StringBuilder("[OpenJML] ").append(lspCommand).append(": ");
        for (int i = 0; i < targets.size(); i++) {
            if (i > 0) sb.append(", ");
            SelectionResolver.Target t = targets.get(i);
            switch (t) {
                case SelectionResolver.Target.File f ->
                    sb.append("file ").append(f.file().getName());
                case SelectionResolver.Target.Method m ->
                    sb.append("method ").append(m.methodFqn());
                case SelectionResolver.Target.Dir d ->
                    sb.append("dir ").append(d.container().getName());
            }
        }
        Console.log(sb.toString());

        for (SelectionResolver.Target target : targets) {
            dispatchTarget(target, event);
        }
        return null;
    }

    /**
     * Dispatch the LSP command for a single {@code target}.
     * Routes to {@link #buildParamsForMethod}, {@link #buildParamsForDir}, or
     * {@link #buildParams} depending on target type.
     */
    private void dispatchTarget(SelectionResolver.Target target, ExecutionEvent event) {
        switch (target) {
            case SelectionResolver.Target.Method m -> {
                IFile file = m.file();
                String uri = file.getLocationURI().toString();
                org.eclipse.jface.text.IDocument doc = getDocument(file);
                buildParamsForMethod(uri, file, m.methodFqn(), event).thenAccept(params -> {
                    if (params == null) return;
                    dispatchCommand(params, doc, file.getProject());
                });
            }
            case SelectionResolver.Target.Dir d -> {
                org.eclipse.core.runtime.IPath loc = d.container().getLocation();
                if (loc == null) {
                    Console.log("[OpenJML] " + lspCommand + ": cannot resolve path for "
                            + d.container().getName());
                    return;
                }
                String dirPath = loc.toOSString();
                buildParamsForDir(dirPath, d.container().getProject(), event).thenAccept(params -> {
                    if (params == null) return;
                    // No specific document for a directory; route via project.
                    dispatchCommand(params, null, d.container().getProject());
                });
            }
            case SelectionResolver.Target.File f -> {
                IFile file = f.file();
                String uri = file.getLocationURI().toString();
                org.eclipse.jface.text.IDocument doc = getDocument(file);
                buildParams(uri, file, event).thenAccept(params -> {
                    if (params == null) return;
                    // computeFirst() waits for server initialisation — do NOT gate it
                    // with anyMatching() (50 ms timeout loses commands during start-up).
                    dispatchCommand(params, doc, file.getProject());
                });
            }
        }
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
     * Build the {@link ExecuteCommandParams} for a whole-file target.
     * Returns a {@code CompletableFuture} so subclasses can do async work.
     * Return {@code null} to cancel.
     */
    protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
            buildParams(String uri, IFile file, ExecutionEvent event) {
        return java.util.concurrent.CompletableFuture.completedFuture(
                new ExecuteCommandParams(lspCommand, List.of(uri)));
    }

    /**
     * Build the {@link ExecuteCommandParams} for a method-level target.
     *
     * <p>The default implementation expands to the whole file (delegates to
     * {@link #buildParams}).  Subclasses that understand method granularity
     * (e.g. {@link RunEsc}) override this to send a method-specific command.
     */
    protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
            buildParamsForMethod(String uri, IFile file, String methodFqn, ExecutionEvent event) {
        // Default: treat the method selection as a file-level request.
        return buildParams(uri, file, event);
    }

    /**
     * Build the {@link ExecuteCommandParams} for a directory target.
     *
     * <p>The default implementation returns {@code null} (skip), since most
     * commands do not support directory-level operation.  Subclasses that do
     * (e.g. {@link RunEsc}) override this to send a directory-based command.
     *
     * @param dirPath  the OS path of the directory
     * @param project  the Eclipse project that contains the directory
     */
    protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
            buildParamsForDir(String dirPath, IProject project, ExecutionEvent event) {
        return java.util.concurrent.CompletableFuture.completedFuture(null); // skip by default
    }

    /**
     * Route {@code params} to the language server.
     * Tries {@code forDocument} then {@code forProject}; if neither finds a server
     * (Optional is empty), falls back to the cached wrapper from LspPartListener.
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
                        Console.log("[OpenJML] ERROR: server not connected — command not sent");
                }
              }).exceptionally(t -> {
                boolean sent = sendViaWrapper(
                        org.jmlspecs.openjml.eclipse.LspPartListener.cachedWrapper, params);
                if (!sent)
                    Console.log("[OpenJML] ERROR: server not connected — command not sent");
                return null;
              });
        } catch (Throwable t) {
            Console.log("[OpenJML] dispatchCommand exception: " + t);
        }
    }

    /**
     * Send {@code params} to the language server via the cached
     * {@code LanguageServerWrapper} from {@link LspPartListener}.
     * Uses reflection to call {@code wrapper.getServer().getWorkspaceService().executeCommand(params)}.
     *
     * @return {@code true} if the call was dispatched (wrapper was non-null and
     *         the reflective call succeeded), {@code false} otherwise
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
            Console.log("[OpenJML] sendViaWrapper failed: " + t);
            return false;
        }
    }

    /**
     * Returns the absolute path of the JDT output folder for {@code file}'s project,
     * or {@code null} if it cannot be determined.
     */
    private static String resolveJdtOutputDir(IFile file) {
        try {
            org.eclipse.jdt.core.IJavaProject jp =
                    org.eclipse.jdt.core.JavaCore.create(file.getProject());
            if (jp == null || !jp.exists()) return null;
            org.eclipse.core.runtime.IPath outputPath = jp.getOutputLocation();
            org.eclipse.core.resources.IFolder folder =
                    org.eclipse.core.resources.ResourcesPlugin.getWorkspace()
                            .getRoot().getFolder(outputPath);
            org.eclipse.core.runtime.IPath location = folder.getLocation();
            return location != null ? location.toOSString() : null;
        } catch (Exception e) {
            Console.log("[OpenJML] resolveJdtOutputDir failed: " + e);
            return null;
        }
    }

    // -----------------------------------------------------------------------
    // Concrete handlers registered via plugin.xml
    // -----------------------------------------------------------------------

    /** Runs {@code openjml.checkJML} on the currently selected entities. */
    public static final class CheckJML extends LspCommandHandler {
        public CheckJML() { super("openjml.checkJML"); }
    }

    /**
     * Runs {@code openjml.runRac} on the currently selected files or directories.
     *
     * <p>Passes the Eclipse project's JDT output folder as the second argument for
     * file targets so the RAC-compiled {@code .class} files land alongside the
     * regular compiled classes and can be executed immediately.
     *
     * <p>Method selections are expanded to the whole containing file (RAC operates
     * at file granularity, not method granularity).
     */
    public static final class RunRac extends LspCommandHandler {
        public RunRac() { super("openjml.runRac"); }

        @Override
        protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
                buildParams(String uri, IFile file, ExecutionEvent event) {
            String outputDir = resolveJdtOutputDir(file);
            List<Object> args = outputDir != null
                    ? List.of(uri, outputDir)
                    : List.of(uri);
            return java.util.concurrent.CompletableFuture.completedFuture(
                    new ExecuteCommandParams("openjml.runRac", args));
        }

        @Override
        protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
                buildParamsForDir(String dirPath, IProject project, ExecutionEvent event) {
            return java.util.concurrent.CompletableFuture.completedFuture(
                    new ExecuteCommandParams("openjml.runRacDir", List.of(dirPath)));
        }
    }

    /**
     * Runs {@code openjml.runEsc} on the currently selected entities.
     *
     * <p>When a method is selected (e.g. in the Outline), dispatches
     * {@code openjml.runEscForMethod} with the method FQN so that only
     * that method is checked.
     *
     * <p>When a project, package, or folder is selected, dispatches
     * {@code openjml.runEscDir} with the directory OS path.
     */
    public static final class RunEsc extends LspCommandHandler {
        public RunEsc() { super("openjml.runEsc"); }

        @Override
        protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
                buildParamsForMethod(String uri, IFile file, String methodFqn, ExecutionEvent event) {
            return java.util.concurrent.CompletableFuture.completedFuture(
                    new ExecuteCommandParams("openjml.runEscForMethod",
                            List.of(uri, methodFqn)));
        }

        @Override
        protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
                buildParamsForDir(String dirPath, IProject project, ExecutionEvent event) {
            return java.util.concurrent.CompletableFuture.completedFuture(
                    new ExecuteCommandParams("openjml.runEscDir", List.of(dirPath)));
        }
    }

    /**
     * Runs {@code openjml.runEscForMethod} on the currently active editor file.
     *
     * <p>This command requires a cursor position and therefore always operates on
     * the active editor, ignoring any view selection.
     *
     * <p>The method FQN is currently passed as an empty string; a future
     * revision can resolve the FQN from the cursor position via the AST.
     */
    public static final class RunEscForMethod extends LspCommandHandler {
        public RunEscForMethod() { super("openjml.runEscForMethod"); }

        /** Always uses the active editor — view selections are ignored. */
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
                if (dialog.open() != 0) return null; // Cancel
                JmlNature.enable(file.getProject());
                // Fall through to dispatch now that the nature is added.
            }

            String uri = file.getLocationURI().toString();
            Console.log(lspCommand + " -> " + uri);

            org.eclipse.jface.text.IDocument doc = null;
            org.eclipse.core.filebuffers.ITextFileBuffer buf =
                    org.eclipse.core.filebuffers.FileBuffers.getTextFileBufferManager()
                            .getTextFileBuffer(file.getFullPath(),
                                    org.eclipse.core.filebuffers.LocationKind.IFILE);
            if (buf != null) doc = buf.getDocument();

            final org.eclipse.jface.text.IDocument finalDoc = doc;
            buildParams(uri, file, event).thenAccept(params -> {
                if (params == null) return;
                dispatchCommand(params, finalDoc, file.getProject());
            });
            return null;
        }

        @Override
        protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
                buildParams(String uri, IFile file, ExecutionEvent event) {
            // TODO: resolve method FQN from cursor position using JDT IMethod.
            // For now send uri + empty string; the server ESCs the whole file
            // when no method name is supplied.
            return java.util.concurrent.CompletableFuture.completedFuture(
                    new ExecuteCommandParams("openjml.runEscForMethod",
                            List.of(uri, "")));
        }
    }

    /**
     * Deletes all OpenJML diagnostic markers from the entire workspace.
     *
     * <p>Unlike the other handlers this does NOT go through LSP.  It operates
     * directly on Eclipse's {@link org.eclipse.core.resources.IMarker} API so
     * that it works even when the language server is not running.
     */
    public static final class ClearMarkers extends AbstractHandler {
        @Override
        public Object execute(ExecutionEvent event) {
            try {
                org.eclipse.core.resources.IWorkspaceRoot root =
                        org.eclipse.core.resources.ResourcesPlugin.getWorkspace().getRoot();
                org.eclipse.core.resources.IMarker[] markers =
                        root.findMarkers(org.eclipse.core.resources.IMarker.PROBLEM,
                                /*includeSubtypes=*/ true,
                                org.eclipse.core.resources.IResource.DEPTH_INFINITE);
                int deleted = 0;
                for (org.eclipse.core.resources.IMarker m : markers) {
                    Object src = m.getAttribute("source");
                    if ("openjml".equals(src)) {
                        m.delete();
                        deleted++;
                    }
                }
                Console.log("[OpenJML] Cleared " + deleted + " OpenJML marker(s).");
            } catch (org.eclipse.core.runtime.CoreException e) {
                Console.log("[OpenJML] ClearMarkers failed: " + e);
            }
            return null;
        }
    }

    /** Sends {@code openjml.clearAndReindex} (no file argument). */
    public static final class ClearAndReindex extends LspCommandHandler {
        public ClearAndReindex() { super("openjml.clearAndReindex"); }

        @Override
        public Object execute(ExecutionEvent event) {
            // clearAndReindex is workspace-wide; no file argument needed.
            // Use any open project to route to the server.
            IEditorPart editor = HandlerUtil.getActiveEditor(event);
            IFile file = null;
            if (editor != null && editor.getEditorInput() instanceof IFileEditorInput fi) {
                file = fi.getFile();
            }

            Console.errorlog(lspCommand);

            if (file != null) {
                org.eclipse.core.filebuffers.ITextFileBuffer buf2 =
                        org.eclipse.core.filebuffers.FileBuffers.getTextFileBufferManager()
                                .getTextFileBuffer(file.getFullPath(),
                                        org.eclipse.core.filebuffers.LocationKind.IFILE);
                org.eclipse.jface.text.IDocument doc2 = (buf2 != null) ? buf2.getDocument() : null;
                ExecuteCommandParams p = new ExecuteCommandParams("openjml.clearAndReindex", List.of());
                if (doc2 != null) {
                    LanguageServers.forDocument(doc2).computeFirst(server ->
                            server.getWorkspaceService().executeCommand(p));
                } else {
                    LanguageServers.forProject(file.getProject()).computeFirst(server ->
                            server.getWorkspaceService().executeCommand(p));
                }
            } else {
                Console.log("OpenJML: no active editor — cannot route clearAndReindex");
            }
            return null;
        }
    }
}
