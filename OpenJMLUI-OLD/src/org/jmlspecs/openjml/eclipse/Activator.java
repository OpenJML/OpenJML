/*
 * This file is part of the OpenJML plug-in project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.net.URL;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;
import org.smtlib.IPos;
import org.smtlib.SMT;

/**
 * The activator class controls the plug-in life cycle. The plug-in is a singleton- there is just one OpenJML Eclipse plug-in in a process.
 */
public class Activator extends AbstractUIPlugin {

    /** The single shared plugin instance */
    private static Activator plugin;

    /** A general utility instance used by the plugin */
    protected Utils utils;

    /** Returns the utility instance for the singleton plugin */
    static public Utils utils() {
        return getDefault().utils;
    }

    /**
     * The constructor, called by Eclipse, not by application code. The Activator is constructed on demand, the first time Eclipse, possibly in response to a user action, invokes a plugin operation.
     */
    public Activator() {
        // Log.log("UI Plugin constructor executed");
        plugin = this;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
     */
    // Called during Activator construction
    public void start(BundleContext context) throws Exception {
        super.start(context);

        // Create the console and connect it to the plugin log (which is connected to the command-line tool log)
        Log.log.setListener(new ConsoleLogger());

        utils = new Utils();

        // Log.log.log("Starting Activator");

        {
            String msg = "Welcome to OpenJML\n\n";
            String javaProjects = "";
            String jmlProjects = "";
            try {
                IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
                IProject[] projects = workspaceRoot.getProjects();
                for (int i = 0; i < projects.length; i++) {
                    IProject project = projects[i];
                    if (project.isOpen() && project.hasNature(JavaCore.NATURE_ID)) {
                        if (JMLNature.isJMLNature(project.getProject())) {
                            jmlProjects += "    " + project.getName() + "\n";
                        } else {
                            javaProjects += "    " + project.getName() + "\n";
                        }
                    }
                }
                if (jmlProjects.isEmpty()) {
                    if (javaProjects.isEmpty()) {
                        msg += "There are no java projects.\n";
                    } else {
                        msg += "None of the Java projects are enabled for automatic JML type-checking on file save.\n";
                    }
                } else {
                    if (javaProjects.isEmpty()) {
                        msg += "All of the Java projects are enabled for automatic JML type-checking on file save.\n";
                    } else {
                        msg += "These Java projects are enabled for automatic JML type-checking on file save:\n" + jmlProjects;
                        msg += "These are not enabled:\n" + javaProjects;
                    }
                }
                msg += "\nEnable existing or new projects for auto-JML-checking using the 'Enable JML on this project' menu command.";
                Utils.showMessageInUI(null, "OpenJML Introduction", msg);
            }
            catch (CoreException ce) {
                Utils.showMessageInUI(null, "OpenJML Introduction", msg + "An error occurred on checking the status of open projects");
                //ce.printStackTracce();
            }
        }

        /**
         * The logic file finder for the plug-in looks for a logic file with the given name: (a) if no logic directory path is set, then it looks within the plugin itself for any built-in files (b) if
         * a logic directory path is set, it looks there.
         * <P>
         * I would have thought that the non-plugin functionality of (a) exporting logics directory and (b) finding the logic files on the classpath would work - but I have not been able to make that
         * function. Thus we need one mechanism for finding resources inside a plug-in (this one - with reference to the plug-in bundle) and another mechanism (looking on the classpath) when one is
         * not inside a plug-in.
         */
        SMT.logicFinder = new SMT.ILogicFinder() {
            @Override
            public InputStream find(SMT.Configuration smtConfig, String name, IPos pos) throws java.io.IOException {
                if (smtConfig == null || smtConfig.logicPath == null || smtConfig.logicPath.trim().length() == 0) {
                    // This logic depends on the fact that the SMT logic files
                    // reside at the root of the jSMTLIB.jar file, and that the
                    // .jar file is part of the plugin.
                    URL url = Platform.getBundle(Env.PLUGIN_ID).getResource(name + org.smtlib.Utils.SUFFIX);
                    if (url != null) {
                        InputStream stream = url.openStream();
                        if (stream != null)
                            return stream;
                    }
                } else {
                    String fname = smtConfig.logicPath + File.separator + name + org.smtlib.Utils.SUFFIX;
                    File f = new File(fname);
                    if (f.isFile())
                        return new FileInputStream(f);
                }
                utils.showMessageInUI(null, "OpenJML - SMT", //$NON-NLS-1$
                                        "No logic file found for " + name); //$NON-NLS-1$
                return null;
            }
        };

        // Initialize the preferences store from system properties
        Options.initialize();

    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
     */
    public void stop(BundleContext context) throws Exception {
        if (Options.uiverboseness) {
            Log.log("JML UI plugin stopping"); //$NON-NLS-1$
        }
        utils = null;
        plugin = null;
        super.stop(context);
    }

    /**
     * Returns the shared instance. 'Default' is an odd name, but it is the typical name used in Eclipse for this purpose.
     * 
     * @return the shared instance
     */
    public static Activator getDefault() {
        return plugin;
    }

}
