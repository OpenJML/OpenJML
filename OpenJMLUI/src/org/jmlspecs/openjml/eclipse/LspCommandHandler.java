/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
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
    
    // FIXME - need to adjust these commands to act on whatever is selected -- a file editor, or possibly multiple items in the Outline or Project Explorer or Package Explorer

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        IEditorPart editor = HandlerUtil.getActiveEditor(event);
        if (editor == null) return null;
        if (!(editor.getEditorInput() instanceof IFileEditorInput)) return null;

        IFile file = ((IFileEditorInput) editor.getEditorInput()).getFile();

        if (!JmlNature.hasNature(file.getProject())) {
            Display.getDefault().asyncExec(() ->
                MessageDialog.openWarning(
                    Display.getDefault().getActiveShell(),
                    "OpenJML — No JML Nature",
                    "Project '" + file.getProject().getName() + "' does not have the OpenJML "
                    + "nature.\n\nUse OpenJML > Add OpenJML Nature to enable checking for "
                    + "this project."));
            return null;
        }

        String uri  = file.getLocationURI().toString();

        Console.log(lspCommand);

        // Obtain the IDocument from the file buffer so we can route via forDocument().
        org.eclipse.jface.text.IDocument doc = null;
        org.eclipse.core.filebuffers.ITextFileBuffer buf =
                org.eclipse.core.filebuffers.FileBuffers.getTextFileBufferManager()
                        .getTextFileBuffer(file.getFullPath(),
                                org.eclipse.core.filebuffers.LocationKind.IFILE);
        if (buf != null) doc = buf.getDocument();

        final org.eclipse.jface.text.IDocument finalDoc = doc;
        buildParams(uri, file, event).thenAccept(params -> {
            if (params == null) return;
            // computeFirst() waits for the server to finish initialising — do NOT
            // gate it with anyMatching() (50 ms timeout causes commands to be lost
            // while the server is still starting up).
            dispatchCommand(params, finalDoc, file.getProject());
        });
        return null;
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
            // computeFirst() waits for server initialisation.  If it routes to a
            // different language server (e.g. JDT) that rejects openjml.* commands,
            // the exceptionally handler retries via the cached OpenJML wrapper.
            java.util.concurrent.CompletableFuture<java.util.Optional<Object>> cf =
                    doc != null
                    ? LanguageServers.forDocument(doc)
                            .computeFirst(s -> s.getWorkspaceService().executeCommand(params))
                    : LanguageServers.forProject(project)
                            .computeFirst(s -> s.getWorkspaceService().executeCommand(params));
            cf.orTimeout(15, java.util.concurrent.TimeUnit.SECONDS)
              .thenAccept(opt -> {
                if (opt == null || opt.isEmpty()) {
                    // No server responded — try the cached OpenJML wrapper directly.
                    boolean sent = sendViaWrapper(
                            org.jmlspecs.openjml.eclipse.LspPartListener.cachedWrapper, params);
                    if (!sent)
                        Console.log("[OpenJML] ERROR: server not connected — command not sent");
                }
              }).exceptionally(t -> {
                // Another server (e.g. JDT) rejected the command — retry via wrapper.
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
            // LanguageServerWrapper.getServer() → LanguageServer proxy
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
            // getServer() returns CompletableFuture<LanguageServer> in some versions,
            // or LanguageServer directly in others.
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
     * Build the {@link ExecuteCommandParams} to send.  Returns a
     * {@code CompletableFuture} so subclasses can do async work (e.g. AST
     * lookups) before the params are ready.  Return {@code null} to cancel.
     */
    protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
            buildParams(String uri, IFile file, ExecutionEvent event) {
        return java.util.concurrent.CompletableFuture.completedFuture(
                new ExecuteCommandParams(lspCommand, List.of(uri)));
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
     * Runs {@code openjml.runRac} on the currently active editor file.
     *
     * <p>Passes the Eclipse project's JDT output folder as the second argument so
     * the RAC-compiled {@code .class} files land alongside the regular compiled
     * classes and can be executed immediately.
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
    }

    /** Runs {@code openjml.runEsc} on the currently seelected entities. */
    public static final class RunEsc extends LspCommandHandler {
        public RunEsc() { super("openjml.runEsc"); }
    }

    /**
     * Runs {@code openjml.runEscForMethod} on the currently active editor file.
     *
     * <p>The method FQN is currently passed as an empty string; a future
     * revision can resolve the FQN from the cursor position via the AST.
     */
    public static final class RunEscForMethod extends LspCommandHandler {
        public RunEscForMethod() { super("openjml.runEscForMethod"); }

        @Override
        protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
                buildParams(String uri, IFile file, ExecutionEvent event) {
            // TODO: resolve method FQN from cursor position using JDT IMethod
            // For now send uri + empty string; the server will ESC the whole file
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
     *
     * <p>Strategy: find all {@code IMarker.PROBLEM} markers on the workspace
     * root (depth = infinite) whose {@code "source"} attribute equals
     * {@code "openjml"}, and delete them.  This attribute is set by the LSP
     * server via {@link DiagnosticConverter} ({@code lsp.setSource("openjml")})
     * and propagated to Eclipse markers by LSP4E — but propagation must be
     * verified by testing.  If the attribute is not propagated, deleting all
     * {@code org.eclipse.lsp4e.diagnostic} markers is a reasonable fallback
     * (see comment in code).
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
            // FIXME - is there some way to get the unique LSP connection for the whole plugin?
            // clearAndReindex is workspace-wide; no file argument needed.
            // Use any open project to route to the server.
            IEditorPart editor = HandlerUtil.getActiveEditor(event);
            IFile file = null;
            if (editor != null && editor.getEditorInput() instanceof IFileEditorInput) {
                file = ((IFileEditorInput) editor.getEditorInput()).getFile();
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
