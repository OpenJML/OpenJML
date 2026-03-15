package openjmlui;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin implements org.eclipse.ui.IStartup {

    // The plug-in ID
    public static final String PLUGIN_ID = "OpenJMLUI"; //$NON-NLS-1$

    // The shared instance
    private static Activator plugin;

    /**
     * Our LSP4E LanguageServerDefinition (LanguageServersRegistry$LanguageServerDefinition),
     * retrieved in earlyStartup() and used by LspPartListener to connect documents.
     */
    static volatile Object ourLsDefinition;

    /** ClassLoader for the org.eclipse.lsp4e bundle — can access its internal classes. */
    static volatile ClassLoader lsp4eLoader;

    /**
     * The constructor
     */
    public Activator() {
        plugin = this;
    }

    /** Called by org.eclipse.ui.startup early in workbench lifecycle. */
    @Override
    public void earlyStartup() {
        System.err.println("[OpenJML] earlyStartup() called");

        // Acquire the lsp4e bundle's classloader (needed for internal classes).
        org.osgi.framework.Bundle lsp4eBundle =
                org.osgi.framework.FrameworkUtil.getBundle(org.eclipse.lsp4e.LanguageServers.class);
        lsp4eLoader = lsp4eBundle.adapt(
                org.osgi.framework.wiring.BundleWiring.class).getClassLoader();

        // Find our LanguageServerDefinition in LanguageServersRegistry and start the server.
        try {
            // LanguageServersRegistry is in the org.eclipse.lsp4e package but not exported;
            // use the lsp4e bundle's own classloader to load it.
            Class<?> regClass = lsp4eLoader.loadClass("org.eclipse.lsp4e.LanguageServersRegistry");

            // Dump LanguageServersRegistry methods (one-time diagnostic).
            System.err.println("[OpenJML] LanguageServersRegistry methods:");
            java.util.Arrays.stream(regClass.getDeclaredMethods())
                    .sorted(java.util.Comparator.comparing(java.lang.reflect.Method::getName))
                    .forEach(m -> System.err.println("[OpenJML]   "
                            + m.getReturnType().getSimpleName() + " " + m.getName() + "("
                            + java.util.Arrays.stream(m.getParameterTypes())
                                    .map(Class::getSimpleName)
                                    .collect(java.util.stream.Collectors.joining(", ")) + ")"));

            Object registry = regClass.getMethod("getInstance").invoke(null);

            // Try getDefinition(String id) — look for method with one String param
            // that returns a LanguageServerDefinition.
            Object def = null;
            for (java.lang.reflect.Method m : regClass.getDeclaredMethods()) {
                if (m.getParameterCount() == 1
                        && m.getParameterTypes()[0] == String.class
                        && m.getName().toLowerCase().contains("def")) {
                    m.setAccessible(true);
                    try {
                        def = m.invoke(registry, "org.jmlspecs.openjml.lsp.server");
                        System.err.println("[OpenJML] " + m.getName() + "() returned: " + def);
                        if (def != null) break;
                    } catch (Exception e2) {
                        System.err.println("[OpenJML] " + m.getName() + "() failed: " + e2);
                    }
                }
            }
            // Fallback: iterate all definitions from any no-arg Collection-returning method
            if (def == null) {
                for (java.lang.reflect.Method m : regClass.getDeclaredMethods()) {
                    if (m.getParameterCount() != 0) continue;
                    m.setAccessible(true);
                    try {
                        Object result = m.invoke(registry);
                        if (result instanceof java.util.Collection) {
                            for (Object item : (java.util.Collection<?>) result) {
                                try {
                                    java.lang.reflect.Field idF = item.getClass().getField("id");
                                    String id = (String) idF.get(item);
                                    System.err.println("[OpenJML] definition id=" + id);
                                    if ("org.jmlspecs.openjml.lsp.server".equals(id)) {
                                        def = item;
                                    }
                                } catch (Exception ignored) {}
                            }
                        }
                    } catch (Exception ignored) {}
                }
            }

            if (def == null) {
                System.err.println("[OpenJML] Our LanguageServerDefinition NOT FOUND in registry");
            } else {
                ourLsDefinition = def;
                System.err.println("[OpenJML] Found our LanguageServerDefinition: " + def);

                // Start the server: LanguageServiceAccessor.startLanguageServer(def)
                Class<?> lsaClass = lsp4eLoader.loadClass("org.eclipse.lsp4e.LanguageServiceAccessor");
                for (java.lang.reflect.Method m : lsaClass.getDeclaredMethods()) {
                    if ("startLanguageServer".equals(m.getName()) && m.getParameterCount() == 1) {
                        m.setAccessible(true);
                        Object wrapper = m.invoke(null, def);
                        System.err.println("[OpenJML] startLanguageServer() returned: " + wrapper);
                        break;
                    }
                }
            }
        } catch (Throwable t) {
            System.err.println("[OpenJML] earlyStartup server start failed: " + t);
            t.printStackTrace(System.err);
        }
    }

    @Override
    public void start(BundleContext context) throws Exception {
        super.start(context);
//        org.jmlspecs.openjml.eclipse.OpenJMLOptions.initializeDefaults(getPreferenceStore());
        // Register part listener to connect documents to the LSP server as files are opened.
        // Must run on the UI thread after workbench is available.
        org.eclipse.swt.widgets.Display.getDefault().asyncExec(() -> {
            try {
                org.eclipse.ui.IWorkbench wb = org.eclipse.ui.PlatformUI.getWorkbench();
                org.jmlspecs.openjml.eclipse.LspPartListener listener =
                        new org.jmlspecs.openjml.eclipse.LspPartListener();
                for (org.eclipse.ui.IWorkbenchWindow w : wb.getWorkbenchWindows()) {
                    org.eclipse.ui.IWorkbenchPage p = w.getActivePage();
                    if (p != null) {
                        p.addPartListener(listener);
                        // Also trigger for editors already open at registration time
                        for (org.eclipse.ui.IEditorReference ref : p.getEditorReferences()) {
                            listener.partOpened(ref);
                        }
                    }
                }
                wb.addWindowListener(new org.eclipse.ui.IWindowListener() {
                    @Override public void windowOpened(org.eclipse.ui.IWorkbenchWindow w) {
                        org.eclipse.ui.IWorkbenchPage p = w.getActivePage();
                        if (p != null) p.addPartListener(listener);
                    }
                    @Override public void windowActivated(org.eclipse.ui.IWorkbenchWindow w) {}
                    @Override public void windowDeactivated(org.eclipse.ui.IWorkbenchWindow w) {}
                    @Override public void windowClosed(org.eclipse.ui.IWorkbenchWindow w) {}
                });
                System.err.println("[OpenJML] LspPartListener registered");
            } catch (Throwable e) {
                System.err.println("[OpenJML] Failed to register LspPartListener: " + e);
                e.printStackTrace(System.err);
            }
        });
        // Diagnostic: verify LSP4E language server extension point and our config elements
        org.eclipse.core.runtime.IExtensionRegistry reg =
                org.eclipse.core.runtime.Platform.getExtensionRegistry();
        org.eclipse.core.runtime.IExtensionPoint ep =
                reg.getExtensionPoint("org.eclipse.lsp4e.languageServer");
        if (ep != null) {
            System.err.println("[OpenJML] lsp4e ext point found, "
                    + ep.getExtensions().length + " extension(s)");
            for (org.eclipse.core.runtime.IExtension ext : ep.getExtensions()) {
                if ("OpenJMLUI".equals(ext.getContributor().getName())) {
                    System.err.println("[OpenJML] Our extension config elements:");
                    for (org.eclipse.core.runtime.IConfigurationElement ce : ext.getConfigurationElements()) {
                        System.err.println("[OpenJML]   <" + ce.getName() + ">");
                        for (org.eclipse.core.runtime.IConfigurationElement child : ce.getChildren()) {
                            System.err.println("[OpenJML]     <" + child.getName()
                                    + " contentTypeId=" + child.getAttribute("contentTypeId")
                                    + " priority=" + child.getAttribute("priority") + ">");
                        }
                    }
                }
            }
        } else {
            System.err.println("[OpenJML] lsp4e ext point NOT FOUND");
        }
    }

    @Override
    public void stop(BundleContext context) throws Exception {
        plugin = null;
        super.stop(context);
    }

    /**
     * Returns the shared instance
     *
     * @return the shared instance
     */
    public static Activator getDefault() {
        return plugin;
    }

}
