package org.openjml.ui;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin implements org.eclipse.ui.IStartup {

    // The plug-in ID
    public static final String PLUGIN_ID = "org.openjml.OpenJMLUI"; //$NON-NLS-1$

    // The shared instance
    private static Activator plugin;

    /** ClassLoader for the org.eclipse.lsp4e bundle — can access its internal classes. */
    public static volatile ClassLoader lsp4eLoader;

    /** The registered part listener; kept so it can be disposed on stop. */
    private static volatile org.jmlspecs.openjml.eclipse.LspPartListener partListener;

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
        // Store the lsp4e bundle's classloader for use by LspPartListener.
        // LSP4E populates LanguageServersRegistry lazily (on first document open),
        // so there is nothing to start here — document connection happens in LspPartListener.
        try {
            org.osgi.framework.Bundle lsp4eBundle =
                    org.osgi.framework.FrameworkUtil.getBundle(
                            org.eclipse.lsp4e.LanguageServers.class);
            lsp4eLoader = lsp4eBundle.adapt(
                    org.osgi.framework.wiring.BundleWiring.class).getClassLoader();
            System.err.println("[OpenJML] lsp4e loader acquired");
        } catch (Throwable t) {
            System.err.println("[OpenJML] earlyStartup failed to acquire lsp4e loader: " + t);
        }
        org.jmlspecs.openjml.eclipse.Console.log("OpenJMLUI plugin started");

        // Proactive check: warn immediately if openjml-lsp is not reachable.
        if (!org.jmlspecs.openjml.eclipse.OpenJMLStreamConnectionProvider.isServerAvailable()) {
            org.jmlspecs.openjml.eclipse.OpenJMLStreamConnectionProvider.showServerNotFoundDialog(
                    org.jmlspecs.openjml.eclipse.OpenJMLStreamConnectionProvider.findServerPath());
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
                partListener = listener;
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
                if ("org.openjml.OpenJMLUI".equals(ext.getContributor().getName())) {
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
        org.jmlspecs.openjml.eclipse.LspPartListener pl = partListener;
        if (pl != null) { pl.dispose(); partListener = null; }
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
