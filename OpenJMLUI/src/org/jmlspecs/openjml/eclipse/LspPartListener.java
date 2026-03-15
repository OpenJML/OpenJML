/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.resources.IFile;
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
 * <p>Registered programmatically from {@link openjmlui.Activator}.
 */
public class LspPartListener implements org.eclipse.ui.IPartListener2 {

    /** Generic Editor ID — last-resort fallback. */
    private static final String GENERIC_EDITOR_ID = "org.eclipse.ui.genericeditor.GenericEditor";

    /** Our LanguageServerDefinition from LanguageServersRegistry, cached after first lookup. */
    private static volatile Object cachedDef;
    /** LanguageServiceAccessor.startLanguageServer(LanguageServerDefinition) method, cached. */
    private static volatile java.lang.reflect.Method startLanguageServerMethod;

    /** Files for which we have already triggered LSP startup. */
    private final java.util.Set<org.eclipse.core.runtime.IPath> triggered =
            java.util.Collections.synchronizedSet(new java.util.HashSet<>());

    @Override public void partOpened(IWorkbenchPartReference ref) { handlePart(ref); }
    @Override public void partActivated(IWorkbenchPartReference ref) { handlePart(ref); }
    @Override public void partBroughtToTop(IWorkbenchPartReference ref) {}
    @Override public void partClosed(IWorkbenchPartReference ref) {}
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

        org.eclipse.core.runtime.IPath path = file.getFullPath();
        if (!triggered.add(path)) return;

        System.err.println("[OpenJML] LspPartListener: handling " + file.getName());

        ClassLoader lsp4eLoader = openjmlui.Activator.lsp4eLoader;
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

                // --- Step 3: connect this document to the (now-running) server ---
                if (wrapper != null && doc != null) {
                    connectDocumentToWrapper(wrapper, doc, file, lsp4eLoader);
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
     * Finds our LanguageServerDefinition in LanguageServersRegistry.
     * Logs all available definitions for diagnostic purposes.
     */
    private static Object findOurDefinition(ClassLoader lsp4eLoader) {
        try {
            Class<?> regClass = lsp4eLoader.loadClass("org.eclipse.lsp4e.LanguageServersRegistry");
            Object registry = regClass.getMethod("getInstance").invoke(null);

            // Try getDefinition(String id) first.
            for (java.lang.reflect.Method m : regClass.getDeclaredMethods()) {
                if (m.getParameterCount() == 1 && m.getParameterTypes()[0] == String.class) {
                    m.setAccessible(true);
                    try {
                        Object def = m.invoke(registry, "org.jmlspecs.openjml.lsp.server");
                        if (def != null) {
                            System.err.println("[OpenJML] Found def via " + m.getName() + ": " + def);
                            return def;
                        }
                    } catch (Exception ignored) {}
                }
            }

            // Fallback: iterate all definitions from any no-arg Collection-returning method.
            System.err.println("[OpenJML] Iterating all LS definitions:");
            for (java.lang.reflect.Method m : regClass.getDeclaredMethods()) {
                if (m.getParameterCount() != 0) continue;
                if (!m.getReturnType().getName().contains("List")
                        && !m.getReturnType().getName().contains("Collection")
                        && !m.getReturnType().getName().contains("Set")) continue;
                m.setAccessible(true);
                try {
                    Object result = m.invoke(registry);
                    if (result instanceof java.util.Collection<?> col) {
                        System.err.println("[OpenJML]   " + m.getName() + "() -> " + col.size() + " items");
                        for (Object item : col) {
                            String id = getStringField(item, "id");
                            String label = getStringField(item, "label");
                            System.err.println("[OpenJML]     id=" + id + " label=" + label
                                    + " class=" + item.getClass().getSimpleName());
                            if ("org.jmlspecs.openjml.lsp.server".equals(id)) {
                                System.err.println("[OpenJML] Found our definition in collection");
                                return item;
                            }
                        }
                    }
                } catch (Exception ignored) {}
            }
            System.err.println("[OpenJML] Our definition NOT found in registry");
        } catch (Throwable t) {
            System.err.println("[OpenJML] findOurDefinition failed: " + t);
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

    private static void connectDocumentToWrapper(Object wrapper, org.eclipse.jface.text.IDocument doc,
            IFile file, ClassLoader lsp4eLoader) {
        // Try connect(IDocument, IFile) first, then connectDocument(IDocument).
        Class<?> wrapperClass = wrapper.getClass();
        for (String methodName : new String[]{"connect", "connectDocument"}) {
            for (java.lang.reflect.Method m : wrapperClass.getDeclaredMethods()) {
                if (!m.getName().equals(methodName)) continue;
                m.setAccessible(true);
                try {
                    if (m.getParameterCount() == 2
                            && m.getParameterTypes()[0].getSimpleName().equals("IDocument")) {
                        m.invoke(wrapper, doc, file);
                        System.err.println("[OpenJML] " + methodName + "(doc, file) called for "
                                + file.getName());
                        return;
                    }
                    if (m.getParameterCount() == 1
                            && m.getParameterTypes()[0].getSimpleName().equals("IDocument")) {
                        m.invoke(wrapper, doc);
                        System.err.println("[OpenJML] " + methodName + "(doc) called for "
                                + file.getName());
                        return;
                    }
                } catch (Exception e) {
                    System.err.println("[OpenJML] " + methodName + "() failed: " + e);
                }
            }
        }
        System.err.println("[OpenJML] No connect method found on wrapper");
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
