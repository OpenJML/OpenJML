/*
 * Copyright (c) 2006-2010 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

  /** The plug-in ID, which must match the content of plugin.xml */
  public static final String PLUGIN_ID = "org.jmlspecs.OpenJMLUI";

  /** The plug-in ID of the Specs project plugin (containing specifications
   * of Java library classes).  This must match the ID specified in the 
   * plugin.xml file of the Specs plugin.  Note that the presence of the
   * Specs plugin is optional, but we use it if it is there.
   */
  public static final String SPECS_PLUGIN_ID = "org.jmlspecs.Specs";
  

  /** The shared instance */
  private static Activator plugin;
  
  /** A general utility instance used by the plugin */
  protected Utils utils;

  /** The instance of the tool's options for the one plugin instance in the UI 
   * version of the OpenJML tool. 
   * This is THE, COMMON, GLOBAL instance of the options structure shared
   * by all projects using this instance of the OpenJML tool. Don't instantiate
   * another one, since this one gets shared by reference in places.  This is
   * initialized by Activator.start().
   * FIXME - perhaps in the future we would support different option sets
   * for different projects; if so we have to worry about separate instances
   * of other parameters not explicitly held in the options structure - e.g. the
   * items held in the UI version of the specspath (listItems).  */
  public static Options options;

  /**
   * The constructor, called by Eclipse, not by user code
   */
  public Activator() {
    //Log.log("UI Plugin constructor executed");
    plugin = this;
  }

  /*
   * (non-Javadoc)
   * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
   */
  public void start(BundleContext context) throws Exception {
    super.start(context);
    Log.log.setListener(new ConsoleLogger("JML Console"));
    //Log.log("JML UI plugin started");
    options = Preferences.extractOptions(null);
    utils = new Utils();
    AbstractPreference.addListener(new AbstractPreference.Listener(){
      public void run() { Preferences.extractOptions(options); }
    });
  }

  /*
   * (non-Javadoc)
   * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
   */
  public void stop(BundleContext context) throws Exception {
    plugin = null;
    options = null;
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

///**
//* Returns an image descriptor for the image file at the given
//* plug-in relative path
//*
//* @param path the path
//* @return the image descriptor
//*/
//public static ImageDescriptor getImageDescriptor(String path) {
//return imageDescriptorFromPlugin(PLUGIN_ID, path);
//}
}
