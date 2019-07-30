/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2005-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.runtime.QualifiedName;
import org.jmlspecs.annotation.NonNull;

/**
 * A class of generally useful quantities that are expected to be
 * constant throughout an execution.
 */
public class Env {

    /**
     * When true, affects some output production to be more amenable to
     * automated testing.  For example, filenames are not printed in
     * error messages, since they will change with changes in testing 
     * platform location of workspace, and reorganization of test sources.
     */
    public static boolean testingMode = false;

    /**
     * A convenience field holding the local system definition of the 
     * end of line character sequence
     */
    public static final String eol = System.getProperty("line.separator"); //$NON-NLS-1$

    /** The plug-in ID, which must match the content of plugin.xml in several places */
    public static final @NonNull
    String PLUGIN_ID = "org.jmlspecs.OpenJMLUI"; //$NON-NLS-1$

    /** The plug-in ID of the Specs project plugin (containing specifications
     * of Java library classes).  This must match the ID specified in the 
     * plugin.xml file of the Specs plugin.  The Specs plugin is the
     * source of all the Java library specifications.
     */
    public static final @NonNull
    String SPECS_PLUGIN_ID = "org.jmlspecs.Specs"; //$NON-NLS-1$

    /** The Eclipse ID of the Decorator used on Java Projects to show that
     * JML compilation is enabled.  This must match the ID defined in the plug-in 
     * definition (plugin.xml).
     */
    static public final @NonNull
    String JML_DECORATOR_ID = Env.PLUGIN_ID + ".JMLDecoration";

    /** String used in openjml-specific properties. */
    final public static @NonNull 
    String OPENJML = "openjml"; //$NON-NLS-1$

    /** The ID of the marker, which must match that in the plugin file. */
    final public static @NonNull 
    String JML_MARKER_ID = Env.PLUGIN_ID + ".JMLProblem"; //$NON-NLS-1$

    /** The ID of the marker, which must match that in the plugin file. */
    final public static @NonNull
    String JML_HIGHLIGHT_ID = Env.PLUGIN_ID + ".JMLHighlight"; //$NON-NLS-1$

    /** The ID of the marker, which must match that in the plugin file. */
    final public static @NonNull
    String JML_HIGHLIGHT_ID_TRUE = JML_HIGHLIGHT_ID + "True"; //$NON-NLS-1$

    /** The ID of the marker, which must match that in the plugin file. */
    final public static @NonNull
    String JML_HIGHLIGHT_ID_FALSE = JML_HIGHLIGHT_ID + "False"; //$NON-NLS-1$

    /** The ID of the marker, which must match that in the plugin file. */
    final public static @NonNull
    String JML_HIGHLIGHT_ID_EXCEPTION = JML_HIGHLIGHT_ID + "Exception"; //$NON-NLS-1$

    /** The ID of the marker, which must match that in the plugin file. */
    final public static @NonNull
    String ESC_MARKER_ID = Env.PLUGIN_ID + ".JMLESCProblem"; //$NON-NLS-1$

    /** The key used to store the sourcepath as a persistent property. */
    @NonNull
    public final static QualifiedName sourceKey = new QualifiedName(PLUGIN_ID,"sourcepath"); //$NON-NLS-1$

    /** The key used to store the specspath as a persistent property. */
    @NonNull
    public final static QualifiedName specsKey = new QualifiedName(PLUGIN_ID,"specspath"); //$NON-NLS-1$

    /** The key used to store the files to rac as a persistent property. */
    @NonNull
    public static final QualifiedName racKey = new QualifiedName(PLUGIN_ID,"racfiles"); //$NON-NLS-1$

    /** ID of the JML project nature. This String is used literally in plugin.xml */
    @NonNull
    public static final String JML_NATURE_ID = PLUGIN_ID + ".JMLNatureID"; //$NON-NLS-1$

    /** The ID of the Java nature */
    @NonNull
    public static final String JAVA_NATURE_ID = "org.eclipse.jdt.core.javanature"; //$NON-NLS-1$

    /** The ID of the Builder, which must match that in the plugin file */
    public static final String JML_BUILDER_ID = PLUGIN_ID + ".JMLBuilder"; //$NON-NLS-1$

}
