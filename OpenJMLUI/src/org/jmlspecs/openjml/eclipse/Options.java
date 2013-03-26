/**
 * This file is part of the OpenJML project.
 * Copyright (c) 2005-2013 David R. Cok.
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.jmlspecs.openjml.Strings;

// FIXME - needs review for all options we're interested in - Options.java; some options may no longer be used

/**
 * This class manages user-settable options for OpenJML - at least those
 * supported by the plug-in. Note that the plug-in uses the usual Eclipse 
 * preference store to persist values of options. The key used for preferences
 * is the same as the key used to specify the option in an openjml.properties
 * file or in a -D command-line option. It consists of a prefix followed by the
 * name of the option as it is specified on the command-line (without the - sign).
 * <P>
 * The OpenJML application itself reads openjml.properties files to read user-set
 * preferences; a plug-in reads the values stored in the preferencesStore.
 * Consequently, the Preferences page of the plug-in has a button to read in
 * any openjml.properties files.
 *
 */
public class Options {
	
	/** Returns the value of a Boolean-valued option. */
	static boolean isOption(String key) {
		//return System.getProperty(key) != null;
		Boolean value = Activator.getDefault().getPreferenceStore().getBoolean(key);
		return value != null && value;
	}
	
	/** Returns the value of a String-valued option. */
	static String value(String key) {
		//return System.getProperty(key) != null;
		return Activator.getDefault().getPreferenceStore().getString(key);
	}
	
	/** The prefix to be put on each key that is a command-line option for the application. */
	final static public String prefix = Strings.optionPropertyPrefix;

	/** A fake preference store key for the update button. */
	final static public String updateKey = prefix + "update"; //$NON-NLS-1$

	// Note: The values of the keys must correspond to the names of the 
	// command-line options.

	/** The preference store key for the checkSpecsPath option. */
	final static public String checkSpecsPathKey = prefix + "checkSpecsPath"; //$NON-NLS-1$
	/** The preference store key for the nonnullByDefault option. */
	final static public String nonnullByDefaultKey = prefix + "nonnullByDefault"; //$NON-NLS-1$
	/** The preference store key for the Java verbosity (boolean). */
	final static public String javaverboseKey = prefix + "verbose"; //$NON-NLS-1$
	/** The preference store key for the verbosity (quiet, nowarnings, verbose) option. */
	final static public String verbosityKey = prefix + "verboseness"; //$NON-NLS-1$
	/** The preference store key for the uiverbosity option. */
	final static public String uiverbosityKey = prefix + "uiverbosity"; //$NON-NLS-1$
	
//	/** The preference store key for the source option. */
//	final static public String sourceKey = prefix + "javaSourceVersion";
//	/** The preference store key for the specsProjectName option. */
//	final static public String specsProjectNameKey = prefix + "specsProjectName";
//	/** The preference store key for the parsePlus option. */
//	final static public String parsePlusKey = prefix + "parsePlus";
	/** The preference store key for the max esc warnings option. */
	final static public String maxWarningsKey = prefix + "maxWarnings"; //$NON-NLS-1$
	/** The preference store key for the check purity option. */
	final static public String noCheckPurityKey = prefix + "noPurityCheck"; //$NON-NLS-1$
	/** The preference store key for the keys option. */
	final static public String optionalKeysKey = prefix + "optionalKeys"; //$NON-NLS-1$
	/** The preference store key for the showNotImplemented option. */
	final static public String showNotImplementedKey = prefix + "showNotImplemented"; //$NON-NLS-1$
	/** The preference store key for the showNotExecutable option. */
	final static public String showNotExecutableKey = prefix + "showNotExecutable"; //$NON-NLS-1$
	/** The preference store key for the noInternalSpecs option. */
	final static public String noInternalSpecsKey = prefix + "noInternalSpecs"; //$NON-NLS-1$
	/** The preference store key for the noInternalRuntime option. */
	final static public String noInternalRuntimeKey = prefix + "noInternalRuntime"; //$NON-NLS-1$

	// TODO - document
	final static public String enableRacKey = prefix + "enableRac"; //$NON-NLS-1$
	final static public String compileToJavaAssert = prefix + "compileToJavaAssert"; //$NON-NLS-1$
	final static public String racNoCheckJavaFeatures = prefix + "racNoCheckJavaFeatures"; //$NON-NLS-1$
	final static public String racNoCheckAssumptions = prefix + "racNoCheckAssumptions"; //$NON-NLS-1$
	final static public String racNoShowSource = prefix + "racNoShowSource"; //$NON-NLS-1$
	
	/** The preference store key for the racbin option */
	final static public String racbinKey = prefix + "racbin";
	
	final static public String defaultProverKey = Strings.defaultProverProperty;
	
	final static public String proverPrefix = Strings.proverPropertyPrefix;
	

}