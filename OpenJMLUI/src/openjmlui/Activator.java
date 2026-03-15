package openjmlui;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin implements org.eclipse.ui.IStartup {

    /** Called by org.eclipse.ui.startup early in workbench lifecycle. */
    @Override
    public void earlyStartup() {
        System.err.println("[OpenJML] earlyStartup() called");

        // 1. Verify our provider can be instantiated (constructor must not throw).
        try {
            org.jmlspecs.openjml.eclipse.OpenJMLStreamConnectionProvider p =
                    new org.jmlspecs.openjml.eclipse.OpenJMLStreamConnectionProvider();
            System.err.println("[OpenJML] Direct instantiation OK: " + p);
        } catch (Throwable t) {
            System.err.println("[OpenJML] Direct instantiation FAILED: " + t);
            t.printStackTrace(System.err);
        }

        // 2. Explore LSP4E 0.18 internals: list top-level classes, then dump public API methods.
        org.osgi.framework.Bundle lsp4eBundle =
                org.osgi.framework.FrameworkUtil.getBundle(org.eclipse.lsp4e.LanguageServers.class);
        ClassLoader lsp4eLoader = lsp4eBundle.adapt(
                org.osgi.framework.wiring.BundleWiring.class).getClassLoader();
        System.err.println("[OpenJML] lsp4e bundle: " + lsp4eBundle.getSymbolicName()
                + " " + lsp4eBundle.getVersion());

        // 2a. List all .class files in the top-level org.eclipse.lsp4e package
        //     so we can find any registry/manager class that may have been renamed.
        try {
            java.util.Enumeration<java.net.URL> entries =
                    lsp4eBundle.findEntries("org/eclipse/lsp4e", "*.class", false);
            System.err.println("[OpenJML] Top-level lsp4e classes:");
            while (entries != null && entries.hasMoreElements()) {
                String p = entries.nextElement().getPath();
                System.err.println("[OpenJML]   " + p.substring(p.lastIndexOf('/') + 1, p.length() - 6));
            }
        } catch (Throwable t) {
            System.err.println("[OpenJML] class listing failed: " + t);
        }

        // 2b. Dump LanguageServiceAccessor methods (exported, @Restricted but accessible at runtime).
        try {
            Class<?> lsa = lsp4eLoader.loadClass("org.eclipse.lsp4e.LanguageServiceAccessor");
            System.err.println("[OpenJML] LanguageServiceAccessor methods:");
            java.util.Arrays.stream(lsa.getDeclaredMethods())
                    .sorted(java.util.Comparator.comparing(java.lang.reflect.Method::getName))
                    .forEach(m -> System.err.println("[OpenJML]   "
                            + m.getReturnType().getSimpleName() + " " + m.getName() + "("
                            + java.util.Arrays.stream(m.getParameterTypes())
                                    .map(Class::getSimpleName)
                                    .collect(java.util.stream.Collectors.joining(", ")) + ")"));
        } catch (Throwable t) {
            System.err.println("[OpenJML] LanguageServiceAccessor dump failed: " + t);
        }

        // 2c. Dump LanguageServers (public API) — look for methods that start new servers.
        try {
            Class<?> ls = org.eclipse.lsp4e.LanguageServers.class;
            System.err.println("[OpenJML] LanguageServers methods:");
            java.util.Arrays.stream(ls.getDeclaredMethods())
                    .sorted(java.util.Comparator.comparing(java.lang.reflect.Method::getName))
                    .forEach(m -> System.err.println("[OpenJML]   "
                            + m.getReturnType().getSimpleName() + " " + m.getName() + "("
                            + java.util.Arrays.stream(m.getParameterTypes())
                                    .map(Class::getSimpleName)
                                    .collect(java.util.stream.Collectors.joining(", ")) + ")"));
            for (Class<?> inner : ls.getDeclaredClasses()) {
                System.err.println("[OpenJML] LanguageServers inner class: " + inner.getSimpleName());
                java.util.Arrays.stream(inner.getDeclaredMethods())
                        .sorted(java.util.Comparator.comparing(java.lang.reflect.Method::getName))
                        .forEach(m -> System.err.println("[OpenJML]     "
                                + m.getReturnType().getSimpleName() + " " + m.getName() + "("
                                + java.util.Arrays.stream(m.getParameterTypes())
                                        .map(Class::getSimpleName)
                                        .collect(java.util.stream.Collectors.joining(", ")) + ")"));
            }
        } catch (Throwable t) {
            System.err.println("[OpenJML] LanguageServers dump failed: " + t);
        }
    }

    // The plug-in ID
    public static final String PLUGIN_ID = "OpenJMLUI"; //$NON-NLS-1$

    // The shared instance
    private static Activator plugin;

    /**
     * The constructor
     */
    public Activator() {
        plugin = this;
    }

    @Override
    public void start(BundleContext context) throws Exception {
        super.start(context);
//        org.jmlspecs.openjml.eclipse.OpenJMLOptions.initializeDefaults(getPreferenceStore());
        // Register part listener to start LSP server when Java/JML files are opened.
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
        // Probe whether ProcessStreamConnectionProvider (and our provider) can be loaded
        // using the same class loader that LSP4E would use (our bundle's loader).
        ClassLoader bundleLoader = getClass().getClassLoader();
        try {
            Class<?> psc = bundleLoader.loadClass(
                    "org.eclipse.lsp4e.server.ProcessStreamConnectionProvider");
            System.err.println("[OpenJML] ProcessStreamConnectionProvider accessible: "
                    + psc.getName());
        } catch (Throwable t) {
            System.err.println("[OpenJML] ProcessStreamConnectionProvider NOT accessible: " + t);
        }
        try {
            Class<?> ours = bundleLoader.loadClass(
                    "org.jmlspecs.openjml.eclipse.OpenJMLStreamConnectionProvider");
            System.err.println("[OpenJML] Our provider loadable: " + ours.getName());
        } catch (Throwable t) {
            System.err.println("[OpenJML] Our provider FAILED to load: " + t);
            t.printStackTrace(System.err);
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
