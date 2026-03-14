package openjmlui;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

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
        // Set LSP preference defaults — no legacy OpenJML class dependencies.
        org.jmlspecs.openjml.eclipse.OpenJMLOptions.initializeDefaults(getPreferenceStore());
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
