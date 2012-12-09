/**
 * Copyright (c) 2005-2011 David R. Cok.
 *
 * @author David R. Cok
 * Jun 18, 2005 
 * 
 */
package org.jmlspecs.openjml.eclipse;

import org.jmlspecs.openjml.Strings;

// FIXME - needs review and cleanup

/**
 * This class holds options that control the global behavior
 * of the application.  If you add a new option, then you should
 * also (a) add code in setDefaults() to provide a default value,
 * (b) add code in CommandLineOptions to provide a way to set 
 * the option from the command line, (c) add code in AbstractPreferences
 * to create a way to persist the value of the option, and (d) add code
 * in Preferences to provide a way to set the option value from the UI.
 *
 */ // TODO - this needs separation from the command-line and from Preferences
public class Options {
	
	static boolean isOption(String key) {
		//return System.getProperty(key) != null;
		Boolean value = Activator.getDefault().getPreferenceStore().getBoolean(key);
		return value != null && value;
	}
	
	static String value(String key) {
		//return System.getProperty(key) != null;
		return Activator.getDefault().getPreferenceStore().getString(key);
	}
	
	/** The prefix to be put on each key. */
	final static public String javaprefix = Strings.javaOptionPropertyPrefix;
	/** The prefix to be put on each key. */
	final static public String prefix = Strings.optionPropertyPrefix;

	/** A fake preference store key for the update button. */
	final static public String updateKey = prefix + "update";

	/** The preference store key for the checkSpecsPath option. */
	final static public String checkSpecsPathKey = prefix + "checkSpecsPath";
	/** The preference store key for the nonnullByDefault option. */
	final static public String nonnullByDefaultKey = prefix + "nonnullByDefault";
	/** The preference store key for the Java verbosity (boolean). */
	final static public String javaverboseKey = prefix + "verbose";
	/** The preference store key for the verbosity (quiet, nowarnings, verbose) option. */
	final static public String verbosityKey = prefix + "verboseness";
	/** The preference store key for the uiverbosity option. */
	final static public String uiverbosityKey = prefix + "uiverbosity";
	
//	/** The preference store key for the source option. */
//	final static public String sourceKey = prefix + "javaSourceVersion";
//	/** The preference store key for the specsProjectName option. */
//	final static public String specsProjectNameKey = prefix + "specsProjectName";
//	/** The preference store key for the parsePlus option. */
//	final static public String parsePlusKey = prefix + "parsePlus";
	/** The preference store key for the check purity option. */
	final static public String checkPurityKey = prefix + "noPurityCheck";
	/** The preference store key for the keys option. */
	final static public String optionalKeysKey = prefix + "optionalKeys";
	/** The preference store key for the showNotImplemented option. */
	final static public String showNotImplementedKey = prefix + "showNotImplemented";
	/** The preference store key for the showNotExecutable option. */
	final static public String showNotExecutableKey = prefix + "showNotExecutable";
	/** The preference store key for the noInternalSpecs option. */
	final static public String noInternalSpecsKey = prefix + "noInternalSpecs";
	/** The preference store key for the noInternalRuntime option. */
	final static public String noInternalRuntimeKey = prefix + "noInternalRuntime";
	/** The preference store key for the autoAddRuntimeToProject option */
	final static public String autoAddRuntimeToProjectKey = prefix + "autoAddRuntimeToProject";

	final static public String enableRacKey = prefix + "enableRac";
	
	/** The preference store key for the racbin option */
	final static public String racbinKey = prefix + "racbin";
	
	final static public String defaultProverKey = Strings.defaultProverProperty;
	
	final static public String proverPrefix = Strings.proverPropertyPrefix;
	

}