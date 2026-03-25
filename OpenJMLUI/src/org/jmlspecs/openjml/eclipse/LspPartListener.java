/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.ITextViewerExtension4;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.part.FileEditorInput;

/**
 * Listens for editor opens and starts the OpenJML LSP server via
 * {@code LanguageServiceAccessor.startLanguageServer(definition)} and then
 * connects each Java/JML document to it.
 *
 * <p>Registered programmatically from {@link org.openjml.ui.Activator}.
 */
public class LspPartListener implements org.eclipse.ui.IPartListener2 {

    /** Singleton instance — set in the constructor so other classes can call static helpers. */
    private static volatile LspPartListener INSTANCE;

    /** Generic Editor ID — last-resort fallback. */
    private static final String GENERIC_EDITOR_ID = "org.eclipse.ui.genericeditor.GenericEditor";

    /** Our LanguageServerDefinition from LanguageServersRegistry, cached after first lookup. */
    private static volatile Object cachedDef;
    /** LanguageServiceAccessor.startLanguageServer(LanguageServerDefinition) method, cached. */
    private static volatile java.lang.reflect.Method startLanguageServerMethod;
    /** The running LanguageServerWrapper, cached after first successful start. */
    static volatile Object cachedWrapper;

    /** A document known to be connected to the server — used to send notifications. */
    static volatile org.eclipse.jface.text.IDocument cachedDocument;

    /** Files for which we have already triggered LSP startup. */
    private final java.util.Set<org.eclipse.core.runtime.IPath> triggered =
            java.util.Collections.synchronizedSet(new java.util.HashSet<>());

    /** JML folding managers keyed by editor part, for cleanup on close. */
    private final java.util.Map<IEditorPart, JmlFoldingManager> foldingManagers =
            new java.util.concurrent.ConcurrentHashMap<>();

    /** JML colorizers for .java editors, keyed by workspace-relative path. */
    private final java.util.Map<org.eclipse.core.runtime.IPath, JmlColorizer> colorizersByPath =
            new java.util.concurrent.ConcurrentHashMap<>();

    public LspPartListener() {
        INSTANCE = this;
    }

    /** Called from Activator.stop(). */
    public void dispose() {
    }

    /**
     * Stops any running LSP server and resets all connection state so that
     * the next editor activation triggers a fresh start at the new path.
     *
     * <p>Called when the {@link OpenJMLOptions#lspServerPathKey} preference changes.
     * Other preference changes use {@link #sendSettingsToServer()} instead.
     *
     * <p>The stop is best-effort: {@code LanguageServerWrapper.stop()} performs
     * a graceful LSP shutdown followed by process destroy.  If that fails the
     * process will be abandoned and the OS will reclaim it.
     */
    public static void restartServer() {
        System.err.println("[OpenJML] restartServer: stopping old server and resetting state");

        // Stop the old server (graceful shutdown + process destroy via lsp4e).
        Object wrapper = cachedWrapper;
        if (wrapper != null) {
            try {
                java.lang.reflect.Method stopMethod = null;
                for (Class<?> c = wrapper.getClass(); c != null; c = c.getSuperclass()) {
                    try { stopMethod = c.getDeclaredMethod("stop"); break; }
                    catch (NoSuchMethodException ignored) {}
                }
                if (stopMethod != null) {
                    stopMethod.setAccessible(true);
                    stopMethod.invoke(wrapper);
                    System.err.println("[OpenJML] restartServer: LanguageServerWrapper.stop() called");
                } else {
                    System.err.println("[OpenJML] restartServer: stop() not found on wrapper");
                }
            } catch (Throwable t) {
                System.err.println("[OpenJML] restartServer: stop() failed: " + t);
            }
        } else {
            System.err.println("[OpenJML] restartServer: no running server to stop");
        }

        // Reset connection state. cachedDef and startLanguageServerMethod are safe
        // to keep — the definition is path-independent and the reflected method
        // is stable across restarts.
        cachedWrapper           = null;
        cachedDocument          = null;
        diagnosticsHookInstalled = false;

        // Clear the per-path trigger set so every open file is reconnected.
        LspPartListener inst = INSTANCE;
        if (inst != null) inst.triggered.clear();

        System.err.println("[OpenJML] restartServer: state reset");

        // Re-trigger partOpened for all open editors so the server starts
        // immediately rather than waiting for the next file activation.
        org.eclipse.swt.widgets.Display.getDefault().asyncExec(() -> {
            LspPartListener listener = INSTANCE;
            if (listener == null) return;
            try {
                for (org.eclipse.ui.IWorkbenchWindow win :
                        org.eclipse.ui.PlatformUI.getWorkbench().getWorkbenchWindows()) {
                    for (org.eclipse.ui.IWorkbenchPage page : win.getPages()) {
                        for (org.eclipse.ui.IEditorReference ref : page.getEditorReferences()) {
                            listener.partOpened(ref);
                        }
                    }
                }
            } catch (Throwable t) {
                System.err.println("[OpenJML] restartServer: re-trigger failed: " + t);
            }
        });
    }

    /**
     * Sends a {@code workspace/didChangeConfiguration} notification to the running
     * LSP server with the current Eclipse preference values.  Safe to call from any
     * thread; no-op if the server wrapper is not yet available.
     *
     * <p>Called from a preference-store {@code IPropertyChangeListener} registered
     * in {@code Activator.earlyStartup()} so that settings changes take effect
     * immediately without restarting the server.
     */
    public static void sendSettingsToServer() {
        org.eclipse.jface.text.IDocument doc = cachedDocument;
        if (doc == null) {
            System.err.println("[OpenJML] sendSettingsToServer: no connected document");
            return;
        }
        try {
            java.util.Map<String, Object> map = OpenJMLOptions.buildInitializationOptions();
            org.eclipse.lsp4j.DidChangeConfigurationParams params =
                    new org.eclipse.lsp4j.DidChangeConfigurationParams(map);
            org.eclipse.lsp4e.LanguageServers.forDocument(doc)
                    .computeAll(ls -> {
                        ls.getWorkspaceService().didChangeConfiguration(params);
                        return java.util.concurrent.CompletableFuture.completedFuture(null);
                    });
            System.err.println("[OpenJML] workspace/didChangeConfiguration sent");
        } catch (Exception e) {
            System.err.println("[OpenJML] sendSettingsToServer failed: " + e);
        }
    }

    /**
     * Disposes all JML folding managers for editors whose file belongs to
     * {@code project}.  Called when the JML nature is removed from a project.
     */
    public static void disposeFoldingManagersForProject(org.eclipse.core.resources.IProject project) {
        LspPartListener inst = INSTANCE;
        if (inst == null) return;
        inst.foldingManagers.entrySet().removeIf(entry -> {
            IEditorPart ep = entry.getKey();
            if (ep.getEditorInput() instanceof IFileEditorInput fi
                    && project.equals(fi.getFile().getProject())) {
                entry.getValue().dispose();
                return true;
            }
            return false;
        });
    }

    @Override public void partOpened(IWorkbenchPartReference ref) { handlePart(ref); }
    @Override public void partActivated(IWorkbenchPartReference ref) { handlePart(ref); }
    @Override public void partBroughtToTop(IWorkbenchPartReference ref) {}
    @Override public void partClosed(IWorkbenchPartReference ref) {
        IWorkbenchPart part = ref.getPart(false);
        if (part instanceof IEditorPart ep) {
            JmlFoldingManager mgr = foldingManagers.remove(ep);
            if (mgr != null) mgr.dispose();
            if (ep.getEditorInput() instanceof IFileEditorInput fi) {
                colorizersByPath.remove(fi.getFile().getFullPath());
            }
        }
    }
    @Override public void partDeactivated(IWorkbenchPartReference ref) {}
    @Override public void partHidden(IWorkbenchPartReference ref) {}
    @Override public void partVisible(IWorkbenchPartReference ref) {}
    @Override public void partInputChanged(IWorkbenchPartReference ref) {}

    private void handlePart(IWorkbenchPartReference ref) {
        IWorkbenchPart part = ref.getPart(false);
        if (!(part instanceof IEditorPart)) return;
        IEditorInput input = ((IEditorPart) part).getEditorInput();
        if (!(input instanceof IFileEditorInput)) return;
        IFile file = ((IFileEditorInput) input).getFile();
        String ext = file.getFileExtension();
        if (!"java".equals(ext) && !"jml".equals(ext)) return;

        // Install JML annotation folding (once per editor instance).
        if (part instanceof IEditorPart ep && !foldingManagers.containsKey(ep)) {
            setupFolding(ep);
        }

        // Install JML semantic-token colorizer for .java files (once per path).
        if ("java".equals(ext) && part instanceof IEditorPart ep
                && !colorizersByPath.containsKey(file.getFullPath())) {
            setupColorizer(ep, file);
        }

        // Retry the diagnostics hook on every activation until it succeeds.
        // (languageClient may be null on first attempt if server hasn't handshaked yet.)
        if (!diagnosticsHookInstalled && cachedWrapper != null) {
            installDiagnosticsHook(cachedWrapper);
        }

        org.eclipse.core.runtime.IPath path = file.getFullPath();
        if (!triggered.add(path)) return;

        System.err.println("[OpenJML] LspPartListener: handling " + file.getName());

        ClassLoader lsp4eLoader = org.openjml.ui.Activator.lsp4eLoader;
        if (lsp4eLoader == null) {
            System.err.println("[OpenJML] LspPartListener: lsp4e loader not ready — using Generic Editor");
            openGenericEditor(file);
            return;
        }

        // Get document from the file buffer (created by JDT when it opened the file).
        org.eclipse.core.filebuffers.ITextFileBuffer buf =
                org.eclipse.core.filebuffers.FileBuffers.getTextFileBufferManager()
                        .getTextFileBuffer(file.getFullPath(),
                                org.eclipse.core.filebuffers.LocationKind.IFILE);
        org.eclipse.jface.text.IDocument doc = (buf != null) ? buf.getDocument() : null;

        // --- Step 1: find our LanguageServerDefinition (cached after first successful lookup) ---
        if (cachedDef == null) {
            cachedDef = findOurDefinition(lsp4eLoader);
        }

        if (cachedDef == null) {
            System.err.println("[OpenJML] LspPartListener: definition not found — using Generic Editor");
            openGenericEditor(file);
            return;
        }

        // --- Step 2: start the server (idempotent — LSP4E skips if already running) ---
        try {
            if (startLanguageServerMethod == null) {
                Class<?> lsaClass = lsp4eLoader.loadClass("org.eclipse.lsp4e.LanguageServiceAccessor");
                for (java.lang.reflect.Method m : lsaClass.getDeclaredMethods()) {
                    if ("startLanguageServer".equals(m.getName()) && m.getParameterCount() == 1) {
                        m.setAccessible(true);
                        startLanguageServerMethod = m;
                        break;
                    }
                }
            }
            if (startLanguageServerMethod != null) {
                Object wrapper = startLanguageServerMethod.invoke(null, cachedDef);
                System.err.println("[OpenJML] LspPartListener: startLanguageServer() = " + wrapper);
                if (wrapper != null) {
                    cachedWrapper = wrapper;
                    installDiagnosticsHook(wrapper);
                }

                // --- Step 3: connect this document to the (now-running) server ---
                if (wrapper != null && doc != null) {
                    java.util.concurrent.CompletableFuture<?> connectFuture =
                            connectDocumentToWrapper(wrapper, doc, file, lsp4eLoader);
                    cachedDocument = doc;  // remember for sendSettingsToServer()
                    // Force code-mining refresh AFTER the connect future completes so that
                    // LanguageServerWrapper.connectedDocuments contains this document before
                    // LSP4E's CodeLensProvider calls LanguageServers.forDocument().
                    final IEditorPart editorSnap = (IEditorPart) part;
                    Runnable refresh = () -> {
                        try {
                            Object adapted = editorSnap.getAdapter(
                                    org.eclipse.jface.text.ITextOperationTarget.class);
                            if (adapted instanceof org.eclipse.jface.text.source.ISourceViewer sv
                                    && sv instanceof org.eclipse.jface.text.source.ISourceViewerExtension5 ext5) {
                                ext5.updateCodeMinings();
                                System.err.println("[OpenJML] code-mining refresh triggered for "
                                        + file.getName());
                            } else {
                                System.err.println("[OpenJML] code-mining refresh: viewer not ISourceViewerExtension5 for "
                                        + file.getName());
                            }
                        } catch (Throwable t) {
                            System.err.println("[OpenJML] updateCodeMinings failed: " + t);
                        }
                    };
                    if (connectFuture != null) {
                        connectFuture.thenRun(
                                () -> org.eclipse.swt.widgets.Display.getDefault().asyncExec(refresh));
                    } else {
                        org.eclipse.swt.widgets.Display.getDefault().asyncExec(refresh);
                    }
                }
            } else {
                System.err.println("[OpenJML] LspPartListener: startLanguageServer method not found");
            }
        } catch (Throwable t) {
            System.err.println("[OpenJML] LspPartListener: start/connect failed: " + t);
            t.printStackTrace(System.err);
        }
    }

    /**
     * Installs JML annotation folding on the given editor.  We delay one event-loop
     * tick so the editor's ProjectionViewer is fully initialised before we query it.
     */
    private void setupFolding(IEditorPart editor) {
        org.eclipse.swt.widgets.Display.getDefault().asyncExec(() -> {
            try {
                Object adapted = editor.getAdapter(org.eclipse.jface.text.ITextOperationTarget.class);
                if (!(adapted instanceof org.eclipse.jface.text.source.projection.ProjectionViewer pv))
                    return;
                JmlFoldingManager mgr = JmlFoldingManager.install(pv);
                if (mgr != null) {
                    foldingManagers.put(editor, mgr);
                    System.err.println("[OpenJML] JML folding installed for "
                            + editor.getEditorInput().getName());
                }
            } catch (Throwable t) {
                System.err.println("[OpenJML] setupFolding failed: " + t);
                t.printStackTrace(System.err);
            }
        });
    }

    /** Ensures the diagnostics hook is installed only once per server instance. */
    private static volatile boolean diagnosticsHookInstalled = false;

    /**
     * Wraps the {@code DefaultLanguageClient}'s diagnostics consumer so that
     * every {@code publishDiagnostics} notification triggers:
     * <ol>
     *   <li>{@link JmlColorizer#refreshAsync()} on the affected document; and</li>
     *   <li>{@link #refreshAllCodeMinings()} on the UI thread so that code-lens
     *       labels update after each ESC / check cycle.</li>
     * </ol>
     *
     * <p>Uses reflection to access the {@code languageClient} field on
     * {@code LanguageServerWrapper} and the {@code setDiagnosticsConsumer} setter on
     * {@code DefaultLanguageClient}.
     */
    private void installDiagnosticsHook(Object wrapper) {
        if (diagnosticsHookInstalled) return;
        // NOTE: do NOT set diagnosticsHookInstalled = true here; only set it on success
        // so that a retry is possible when languageClient is null at startup.
        try {
            // Reflectively get wrapper.languageClient (DefaultLanguageClient)
            java.lang.reflect.Field clientField = null;
            for (Class<?> c = wrapper.getClass(); c != null; c = c.getSuperclass()) {
                try { clientField = c.getDeclaredField("languageClient"); break; }
                catch (NoSuchFieldException ignored) {}
            }
            if (clientField == null) {
                // The field was not found in any superclass — this is a permanent failure.
                System.err.println("[OpenJML] diagnosticsHook: languageClient field not found");
                diagnosticsHookInstalled = true;  // don't retry
                return;
            }
            clientField.setAccessible(true);
            Object client = clientField.get(wrapper);
            if (client == null) {
                // Server not yet initialized — languageClient assigned after handshake.
                // Leave diagnosticsHookInstalled = false so the next handlePart call retries.
                System.err.println("[OpenJML] diagnosticsHook: languageClient is null (will retry)");
                return;
            }

            // Get the existing diagnosticConsumer to wrap it
            java.lang.reflect.Field consumerField = null;
            for (Class<?> c = client.getClass(); c != null; c = c.getSuperclass()) {
                try { consumerField = c.getDeclaredField("diagnosticConsumer"); break; }
                catch (NoSuchFieldException ignored) {}
            }
            @SuppressWarnings("unchecked")
            java.util.function.Consumer<Object> original = (consumerField != null)
                    ? (java.util.function.Consumer<Object>) getField(consumerField, client)
                    : null;

            // Install a wrapper consumer that calls the original then refreshes colorizers
            java.lang.reflect.Method setter = null;
            for (java.lang.reflect.Method m : client.getClass().getMethods()) {
                if ("setDiagnosticsConsumer".equals(m.getName()) && m.getParameterCount() == 1) {
                    setter = m; break;
                }
            }
            if (setter == null) {
                System.err.println("[OpenJML] diagnosticsHook: setDiagnosticsConsumer not found");
                return;
            }
            final java.util.function.Consumer<Object> orig = original;
            java.util.function.Consumer<Object> wrapped = params -> {
                if (orig != null) orig.accept(params);
                try {
                    String uri = (String) params.getClass().getMethod("getUri").invoke(params);
                    if (uri != null) refreshColorizerForUri(uri);
                } catch (Exception ignored) {}
                // Schedule a code-mining refresh on the UI thread.  lsp4e's
                // DefaultLanguageClient.refreshCodeLenses() runs updateCodeMinings() on
                // ForkJoinPool where UI.getActivePage() returns null (a no-op).
                // We bypass that and call updateCodeMinings() directly on each viewer.
                System.err.println("[OpenJML] diagnosticsHook: scheduling refreshAllCodeMinings");
                org.eclipse.swt.widgets.Display.getDefault().asyncExec(LspPartListener::refreshAllCodeMinings);
            };
            setter.invoke(client, wrapped);
            diagnosticsHookInstalled = true;  // success — don't install again
            System.err.println("[OpenJML] diagnosticsHook installed");
        } catch (Throwable t) {
            System.err.println("[OpenJML] installDiagnosticsHook failed: " + t);
            t.printStackTrace(System.err);
        }
    }

    private static Object getField(java.lang.reflect.Field f, Object obj) {
        try { f.setAccessible(true); return f.get(obj); } catch (Exception e) { return null; }
    }

    /** Finds the colorizer registered for the given file URI and refreshes it. */
    private void refreshColorizerForUri(String fileUri) {
        try {
            java.net.URI uri = java.net.URI.create(fileUri);
            IFile[] files = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(uri);
            for (IFile f : files) {
                JmlColorizer c = colorizersByPath.get(f.getFullPath());
                if (c != null) {
                    // .java files: JmlColorizer overlays JML tokens on JDT's presentation.
                    c.refreshAsync();
                } else if ("jml".equals(f.getFileExtension())) {
                    // .jml files: LSP4E's SemanticTokensPresentationReconciler handles tokens,
                    // but it only runs on document edits — not when the server sends fresh tokens
                    // after a check.  Invalidate the presentation so it re-requests tokens now.
                    invalidateJmlEditorPresentation(f);
                }
            }
        } catch (Exception e) {
            System.err.println("[OpenJML] refreshColorizerForUri error: " + e);
        }
    }

    /** Invalidates the text presentation for any editor showing {@code file}. */
    private static void invalidateJmlEditorPresentation(IFile file) {
        org.eclipse.swt.widgets.Display.getDefault().asyncExec(() -> {
            try {
                for (org.eclipse.ui.IWorkbenchWindow w :
                        org.eclipse.ui.PlatformUI.getWorkbench().getWorkbenchWindows()) {
                    for (org.eclipse.ui.IWorkbenchPage p : w.getPages()) {
                        for (org.eclipse.ui.IEditorReference ref : p.getEditorReferences()) {
                            org.eclipse.ui.IEditorPart ed = ref.getEditor(false);
                            if (ed == null) continue;
                            if (!(ed.getEditorInput() instanceof IFileEditorInput fi)) continue;
                            if (!file.equals(fi.getFile())) continue;
                            Object adapted = ed.getAdapter(
                                    org.eclipse.jface.text.ITextOperationTarget.class);
                            if (adapted instanceof ITextViewer tv) {
                                // Trigger LSP4E's SemanticTokensPresentationReconciler to
                                // re-request semanticTokens/full.  It only runs on document
                                // edits, so the first check after open would otherwise leave
                                // the .jml file uncolored until the user makes an edit.
                                tv.invalidateTextPresentation();
                            }
                        }
                    }
                }
            } catch (Exception e) {
                System.err.println("[OpenJML] invalidateJmlEditorPresentation: " + e);
            }
        });
    }

    /**
     * Attaches a {@link JmlColorizer} to the given {@code .java} editor's viewer.
     * The colorizer overlays JML semantic-token colors (keyword / macro / variable)
     * on top of JDT's own syntax coloring, which would otherwise render
     * {@code //@ …} annotations as plain comments.
     */
    private void setupColorizer(IEditorPart editor, IFile file) {
        org.eclipse.swt.widgets.Display.getDefault().asyncExec(() -> {
            try {
                Object adapted = editor.getAdapter(org.eclipse.jface.text.ITextOperationTarget.class);
                if (!(adapted instanceof ITextViewer viewer)) return;
                if (!(viewer instanceof ITextViewerExtension4 ext4)) return;
                org.eclipse.jface.text.IDocument doc = viewer.getDocument();
                if (doc == null) return;
                JmlColorizer.ensureColors();
                JmlColorizer colorizer = new JmlColorizer(viewer, doc);
                ext4.addTextPresentationListener(colorizer);
                colorizersByPath.put(file.getFullPath(), colorizer);
                System.err.println("[OpenJML] JML colorizer installed for " + file.getName());
                // Immediate fetch — gets cached tokens if a prior check has already run.
                colorizer.refreshAsync();
            } catch (Throwable t) {
                System.err.println("[OpenJML] setupColorizer failed: " + t);
                t.printStackTrace(System.err);
            }
        });
    }

    /**
     * Constructs our LanguageServerDefinition directly from our IConfigurationElement
     * rather than looking it up in LanguageServersRegistry (which may not have processed
     * our extension by the time this is called).
     *
     * Strategy:
     *  1. Find our IConfigurationElement in Eclipse's extension registry.
     *  2. Obtain the ExtensionLanguageServerDefinition class from an existing registry entry.
     *  3. Reflectively instantiate it with our IConfigurationElement.
     */
    private static Object findOurDefinition(ClassLoader lsp4eLoader) {
        try {
            // --- Step 1: find our IConfigurationElement ---
            org.eclipse.core.runtime.IExtensionRegistry extReg =
                    org.eclipse.core.runtime.Platform.getExtensionRegistry();
            org.eclipse.core.runtime.IExtensionPoint ep =
                    extReg.getExtensionPoint("org.eclipse.lsp4e.languageServer");
            if (ep == null) {
                System.err.println("[OpenJML] lsp4e.languageServer extension point not found");
                return null;
            }
            org.eclipse.core.runtime.IConfigurationElement ourCE = null;
            for (org.eclipse.core.runtime.IExtension ext : ep.getExtensions()) {
                if ("org.openjml.OpenJMLUI".equals(ext.getContributor().getName())) {
                    for (org.eclipse.core.runtime.IConfigurationElement ce
                            : ext.getConfigurationElements()) {
                        if ("languageServer".equals(ce.getName())) {
                            ourCE = ce;
                            break;
                        }
                    }
                }
            }
            if (ourCE == null) {
                System.err.println("[OpenJML] Our IConfigurationElement not found");
                return null;
            }
            System.err.println("[OpenJML] Found our IConfigurationElement id="
                    + ourCE.getAttribute("id"));

            // --- Step 2: get the ExtensionLanguageServerDefinition class from an existing entry ---
            Class<?> regClass = lsp4eLoader.loadClass("org.eclipse.lsp4e.LanguageServersRegistry");
            Object registry = regClass.getMethod("getInstance").invoke(null);
            Class<?> defClass = null;
            for (java.lang.reflect.Method m : regClass.getDeclaredMethods()) {
                if (m.getParameterCount() != 0) continue;
                String rn = m.getReturnType().getName();
                if (!rn.contains("List") && !rn.contains("Collection") && !rn.contains("Set"))
                    continue;
                m.setAccessible(true);
                try {
                    Object result = m.invoke(registry);
                    if (!(result instanceof java.util.Collection<?> col) || col.isEmpty()) continue;
                    Object first = col.iterator().next();
                    Object val = first.getClass().getMethod("getValue").invoke(first);
                    if (val != null) {
                        defClass = val.getClass();
                        System.err.println("[OpenJML] ExtensionLanguageServerDefinition class: "
                                + defClass.getName());
                        break;
                    }
                } catch (Exception ignored) {}
            }
            if (defClass == null) {
                System.err.println("[OpenJML] Could not resolve ExtensionLanguageServerDefinition class");
                return null;
            }

            // --- Step 3: construct our definition from ourCE ---
            for (java.lang.reflect.Constructor<?> ctor : defClass.getDeclaredConstructors()) {
                Class<?>[] pts = ctor.getParameterTypes();
                if (pts.length == 1 && pts[0].isAssignableFrom(ourCE.getClass())) {
                    ctor.setAccessible(true);
                    Object def = ctor.newInstance(ourCE);
                    System.err.println("[OpenJML] Created LanguageServerDefinition: " + def);
                    return def;
                }
            }
            // If exact match failed, try by interface name
            for (java.lang.reflect.Constructor<?> ctor : defClass.getDeclaredConstructors()) {
                Class<?>[] pts = ctor.getParameterTypes();
                if (pts.length == 1 && pts[0].getName().contains("ConfigurationElement")) {
                    ctor.setAccessible(true);
                    Object def = ctor.newInstance(ourCE);
                    System.err.println("[OpenJML] Created LanguageServerDefinition (by name): " + def);
                    return def;
                }
            }
            System.err.println("[OpenJML] No matching constructor on " + defClass.getName()
                    + "; available:");
            for (java.lang.reflect.Constructor<?> c : defClass.getDeclaredConstructors()) {
                System.err.println("[OpenJML]   " + c);
            }
        } catch (Throwable t) {
            System.err.println("[OpenJML] findOurDefinition failed: " + t);
            t.printStackTrace(System.err);
        }
        return null;
    }

    /** Returns all declared fields from cls and all its superclasses. */
    private static java.util.List<java.lang.reflect.Field> getAllDeclaredFields(Class<?> cls) {
        java.util.List<java.lang.reflect.Field> fields = new java.util.ArrayList<>();
        for (Class<?> c = cls; c != null && c != Object.class; c = c.getSuperclass()) {
            fields.addAll(java.util.Arrays.asList(c.getDeclaredFields()));
        }
        return fields;
    }

    /**
     * Extracts the nested LanguageServerDefinition from a
     * ContentTypeToLanguageServerDefinition (which extends
     * AbstractMap.SimpleEntry&lt;IContentType, LanguageServerDefinition&gt;).
     * Tries getValue() first; falls back to scanning field values.
     */
    private static Object findNestedDef(Object item) {
        // Primary: AbstractMap.SimpleEntry.getValue() returns the LanguageServerDefinition.
        try {
            java.lang.reflect.Method getVal = item.getClass().getMethod("getValue");
            Object v = getVal.invoke(item);
            if (v != null && v.getClass().getName().contains("LanguageServerDefinition")) {
                return v;
            }
        } catch (Exception ignored) {}
        // Fallback: scan all field values.
        for (java.lang.reflect.Field f : getAllDeclaredFields(item.getClass())) {
            try {
                f.setAccessible(true);
                Object v = f.get(item);
                if (v != null && v.getClass().getName().contains("LanguageServerDefinition")) {
                    return v;
                }
            } catch (Exception ignored) {}
        }
        return null;
    }

    private static String getStringField(Object obj, String fieldName) {
        try {
            java.lang.reflect.Field f = obj.getClass().getDeclaredField(fieldName);
            f.setAccessible(true);
            Object v = f.get(obj);
            return v != null ? v.toString() : "null";
        } catch (Exception e) {
            // Try superclass
            try {
                Class<?> c = obj.getClass().getSuperclass();
                while (c != null) {
                    try {
                        java.lang.reflect.Field f = c.getDeclaredField(fieldName);
                        f.setAccessible(true);
                        Object v = f.get(obj);
                        return v != null ? v.toString() : "null";
                    } catch (NoSuchFieldException ignored) {}
                    c = c.getSuperclass();
                }
            } catch (Exception ignored) {}
            return "?";
        }
    }

    /**
     * Calls {@code updateCodeMinings()} on every open editor's source viewer so that
     * LSP4E's {@code CodeLensProvider} re-queries the server.  Must run on the UI thread.
     *
     * <p>LSP4E's own {@code DefaultLanguageClient.refreshCodeLenses()} wraps
     * {@code updateCodeMinings()} in {@code CompletableFuture.runAsync()} (ForkJoinPool)
     * where {@code UI.getActivePage()} returns null, making it a no-op.  We bypass
     * {@code DefaultLanguageClient} entirely and walk all viewers directly using
     * {@code getWorkbenchWindows()} (which works even when Eclipse does not have OS focus).
     */
    private static void refreshAllCodeMinings() {
        try {
            org.eclipse.ui.IWorkbench wb = org.eclipse.ui.PlatformUI.getWorkbench();
            int updated = 0;
            for (org.eclipse.ui.IWorkbenchWindow win : wb.getWorkbenchWindows()) {
                for (org.eclipse.ui.IWorkbenchPage page : win.getPages()) {
                    for (org.eclipse.ui.IEditorReference ref : page.getEditorReferences()) {
                        org.eclipse.ui.IEditorPart editor = ref.getEditor(false);
                        if (editor == null) continue;
                        Object adapted = editor.getAdapter(org.eclipse.jface.text.ITextViewer.class);
                        if (adapted == null)
                            adapted = editor.getAdapter(org.eclipse.jface.text.ITextOperationTarget.class);
                        if (adapted == null) continue;
                        logCodeMiningState(adapted, editor.getTitle());
                        if (adapted instanceof org.eclipse.jface.text.source.ISourceViewerExtension5 ext5) {
                            ext5.updateCodeMinings();
                            updated++;
                            System.err.println("[OpenJML] refreshAllCodeMinings: updateCodeMinings() for " + editor.getTitle());
                        } else {
                            System.err.println("[OpenJML] refreshAllCodeMinings: viewer not ISourceViewerExtension5 for "
                                    + editor.getTitle() + " (" + adapted.getClass().getSimpleName() + ")");
                        }
                    }
                }
            }
            System.err.println("[OpenJML] refreshAllCodeMinings: updated " + updated + " viewer(s)");
        } catch (Throwable t) {
            System.err.println("[OpenJML] refreshAllCodeMinings failed: " + t);
        }
    }

    /** Logs the code mining manager and provider state of a viewer (diagnostic only). */
    private static void logCodeMiningState(Object viewer, String editorTitle) {
        try {
            java.lang.reflect.Field fMgr = null, fProv = null;
            for (Class<?> c = viewer.getClass(); c != null; c = c.getSuperclass()) {
                if (fMgr == null) try { fMgr = c.getDeclaredField("fCodeMiningManager"); } catch (NoSuchFieldException ignored) {}
                if (fProv == null) try { fProv = c.getDeclaredField("fCodeMiningProviders"); } catch (NoSuchFieldException ignored) {}
                if (fMgr != null && fProv != null) break;
            }
            String mgrStr = "field not found";
            if (fMgr != null) { fMgr.setAccessible(true); Object v = fMgr.get(viewer); mgrStr = v == null ? "null" : v.getClass().getSimpleName(); }
            String provStr = "field not found";
            if (fProv != null) {
                fProv.setAccessible(true);
                Object arr = fProv.get(viewer);
                if (arr instanceof Object[] pa) {
                    StringBuilder sb = new StringBuilder("[");
                    for (Object p : pa) sb.append(p == null ? "null" : p.getClass().getSimpleName()).append(", ");
                    sb.append("]");
                    provStr = sb.toString();
                } else { provStr = String.valueOf(arr); }
            }
            System.err.println("[OpenJML] " + editorTitle + " fCodeMiningManager=" + mgrStr + " providers=" + provStr);
        } catch (Throwable ignored) {}
    }

    @SuppressWarnings("unchecked")
    private static java.util.concurrent.CompletableFuture<?> connectDocumentToWrapper(
            Object wrapper, org.eclipse.jface.text.IDocument doc,
            IFile file, ClassLoader lsp4eLoader) {
        // Walk the full class hierarchy so inherited methods are found.
        Class<?> wrapperClass = wrapper.getClass();
        java.util.List<java.lang.reflect.Method> allMethods = new java.util.ArrayList<>();
        for (Class<?> c = wrapperClass; c != null && c != Object.class; c = c.getSuperclass()) {
            allMethods.addAll(java.util.Arrays.asList(c.getDeclaredMethods()));
        }

        // Log all available connect-like methods to help diagnose signature mismatches.
        for (java.lang.reflect.Method m : allMethods) {
            if (m.getName().startsWith("connect")) {
                System.err.println("[OpenJML] wrapper has: " + m.getName()
                        + java.util.Arrays.toString(m.getParameterTypes()));
            }
        }

        org.eclipse.core.runtime.IPath ipath = file.getFullPath();

        for (String methodName : new String[]{"connect", "connectDocument"}) {
            for (java.lang.reflect.Method m : allMethods) {
                if (!m.getName().equals(methodName)) continue;
                m.setAccessible(true);
                Class<?>[] pts = m.getParameterTypes();
                try {
                    // LSP4E 0.19+: connect(IPath, IDocument)
                    if (pts.length == 2
                            && pts[0].getSimpleName().equals("IPath")
                            && pts[1].getSimpleName().equals("IDocument")) {
                        Object r = m.invoke(wrapper, ipath, doc);
                        System.err.println("[OpenJML] " + methodName + "(IPath, IDocument) called for "
                                + file.getName());
                        return (r instanceof java.util.concurrent.CompletableFuture<?> cf) ? cf : null;
                    }
                    // connect(IDocument, IFile/IPath) — doc first
                    if (pts.length == 2
                            && pts[0].getSimpleName().equals("IDocument")) {
                        Object r = m.invoke(wrapper, doc, file);
                        System.err.println("[OpenJML] " + methodName + "(IDocument, file) called for "
                                + file.getName());
                        return (r instanceof java.util.concurrent.CompletableFuture<?> cf) ? cf : null;
                    }
                    // connect(IDocument)
                    if (pts.length == 1
                            && pts[0].getSimpleName().equals("IDocument")) {
                        Object r = m.invoke(wrapper, doc);
                        System.err.println("[OpenJML] " + methodName + "(IDocument) called for "
                                + file.getName());
                        return (r instanceof java.util.concurrent.CompletableFuture<?> cf) ? cf : null;
                    }
                } catch (Exception e) {
                    System.err.println("[OpenJML] " + methodName + "() invocation failed: " + e);
                }
            }
        }
        System.err.println("[OpenJML] No connect method matched on "
                + wrapperClass.getName() + " for " + file.getName());
        return null;
    }

    private void openGenericEditor(IFile file) {
        try {
            org.eclipse.ui.IWorkbenchPage page =
                    org.eclipse.ui.PlatformUI.getWorkbench().getActiveWorkbenchWindow()
                            .getActivePage();
            if (page == null) return;
            IEditorPart ge = page.openEditor(new FileEditorInput(file), GENERIC_EDITOR_ID, false);
            System.err.println("[OpenJML] LspPartListener: Generic Editor fallback: " + (ge != null));
        } catch (Throwable e) {
            System.err.println("[OpenJML] LspPartListener: Generic Editor fallback failed: " + e);
        }
    }
}
