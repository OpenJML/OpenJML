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
 * <p>Registered programmatically from {@link org.openjml.ui.Activator}.
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

    private static void connectDocumentToWrapper(Object wrapper, org.eclipse.jface.text.IDocument doc,
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
                        m.invoke(wrapper, ipath, doc);
                        System.err.println("[OpenJML] " + methodName + "(IPath, IDocument) called for "
                                + file.getName());
                        return;
                    }
                    // connect(IDocument, IFile/IPath) — doc first
                    if (pts.length == 2
                            && pts[0].getSimpleName().equals("IDocument")) {
                        m.invoke(wrapper, doc, file);
                        System.err.println("[OpenJML] " + methodName + "(IDocument, file) called for "
                                + file.getName());
                        return;
                    }
                    // connect(IDocument)
                    if (pts.length == 1
                            && pts[0].getSimpleName().equals("IDocument")) {
                        m.invoke(wrapper, doc);
                        System.err.println("[OpenJML] " + methodName + "(IDocument) called for "
                                + file.getName());
                        return;
                    }
                } catch (Exception e) {
                    System.err.println("[OpenJML] " + methodName + "() invocation failed: " + e);
                }
            }
        }
        System.err.println("[OpenJML] No connect method matched on "
                + wrapperClass.getName() + " for " + file.getName());
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
