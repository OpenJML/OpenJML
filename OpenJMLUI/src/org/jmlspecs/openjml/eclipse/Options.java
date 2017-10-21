/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2005-2013 David R. Cok.
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.lang.reflect.Field;
import java.util.Properties;

import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.Strings;

import com.sun.tools.javac.util.Context;

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
		Boolean value = Activator.getDefault().getPreferenceStore().getBoolean(key);
		return value != null && value;
	}
	
	/** Returns the value of a String-valued option. */
	static String value(String key) {
		return Activator.getDefault().getPreferenceStore().getString(key);
	}
	
	/** Sets the value of a String-valued option. */
	static void setValue(String key, String value) {
		Activator.getDefault().getPreferenceStore().setValue(key,value);
	}
	
	/** Cached value of the verboseness */
	static public boolean uiverboseness = false;

	/** Caches values of properties as needed, based on preference store */
	public static void cache() {
		Options.uiverboseness = Options.isOption(Options.uiverbosityKey);
	}
	
    public void setStoreToDefaults() {
    	IPreferenceStore store = Activator.getDefault().getPreferenceStore();
    	for (Field f: Options.class.getDeclaredFields()) {
    		String fieldName = f.getName();
    		if (fieldName.endsWith("Key")) {
    			try {
    				String key = f.get(null).toString(); // value of the field
    				store.setToDefault(key);
    			} catch (IllegalAccessException e) {
    				// Should never happen
    			}
    		}
    	}
    }
    

	
	/** Initializes preference store from properties and JmlOptions */
	public static void initialize() {
		IPreferenceStore store = Activator.getDefault().getPreferenceStore();
		boolean b = store.getBoolean(Options.alreadyInitializedKey);
		boolean bb = store.getBoolean(Options.initializeOnStartupKey);
		if (!b || bb) {
			Properties properties = org.jmlspecs.openjml.Utils.findProperties(null);
			for (java.util.Map.Entry<Object,Object> entry: properties.entrySet()) {
				String key = entry.getKey().toString();
				String value = entry.getValue().toString();
				if (key.startsWith(Strings.optionPropertyPrefix)) {
					boolean isBoolean = false;
					String optname = "-" + key.substring(Strings.optionPropertyPrefix.length());
					for (JmlOption o: JmlOption.values()) {
						if (o.optionName().equals(optname)) {
							isBoolean = !o.hasArg();
							break;
						}
					}
					if (isBoolean) {
						store.setValue(key, Boolean.parseBoolean(value));
					} else {
						store.setValue(key, value);
					}
				}
			}
			store.setValue(Options.alreadyInitializedKey,true);
		}
		Options.cache();
	}
	
//	public static void initialize(boolean override, Context context) {
//		IPreferenceStore store = Activator.getDefault().getPreferenceStore();
//		for (JmlOption opt: JmlOption.values()) {
//			String key = Strings.optionPropertyPrefix + opt.optionName().substring(1); // The substring is to remove the initial hyphen
//			if (override || !store.contains(key)) {
//				store.putValue(key, opt.defaultValue().toString());
//			}
//		}
//	}


	/** The preference key for a JmlOption */
	public static String key(JmlOption opt) {
		return prefix + opt.optionName().substring(1);
	}
	
	/** The preference key for a non-JmlOption */
	public static String key(String s) {
		return prefix + s;
	}
	
	// Note: The values of the keys must correspond to the names of the 
	// command-line options. That way we can load them automatically.

	/** The prefix to be put on each key that is a command-line option for the application. */
	final static public String prefix = Strings.optionPropertyPrefix;

	/** A fake preference store key for the update button. */
	final static public String updateKey = prefix + "update"; //$NON-NLS-1$

	final static public String alreadyInitializedKey = prefix + "alreadyInitialized";
	/** The preference store key for the initialize on startup button */
	final static public String initializeOnStartupKey = prefix + "initializeOnStartup";
	
	/** The preference store key for the checkSpecsPath option. */
	final static public String checkSpecsPathKey = key(JmlOption.CHECKSPECSPATH);
	/** The preference store key for the nonnullByDefault option. */
	final static public String nullableByDefaultKey = key(JmlOption.NULLABLEBYDEFAULT);
	/** The preference store key for the Java verbosity (boolean). */
	final static public String javaverboseKey = prefix + "verbose"; //$NON-NLS-1$
	/** The preference store key for the verbosity (quiet, nowarnings, verbose) option. */
	final static public String verbosityKey = prefix + "verboseness"; //$NON-NLS-1$
	/** The preference store key for the uiverbosity option. */
	final static public String uiverbosityKey = prefix + "uiverbosity"; //$NON-NLS-1$
	/** The preference store key for the show-error-popups UI control. */
	final static public String showErrorPopupsKey = prefix + "showErrorPopups"; //$NON-NLS-1$
	/** The preference store key for the -show option. */
	final static public String showKey = key(JmlOption.SHOW);
	/** The preference store key for the -checkFeasibility option. */
	final static public String feasibilityKey = key(JmlOption.FEASIBILITY);
	
//	/** The preference store key for the show trace info option. */
//	final static public String traceKey = prefix + "trace"; //$NON-NLS-1$
//	/** The preference store key for the -subexpressions option. */
//	final static public String subexpressionsKey = prefix + "subexpressions"; //$NON-NLS-1$
	/** The preference store key for the max esc warnings option. */
	final static public String escMaxWarningsKey = key(JmlOption.ESC_MAX_WARNINGS);
	/** The preference store key for the strict JML option. */
	final static public String strictKey = key(JmlOption.STRICT);
	/** The preference store key for the check purity option. */
	final static public String purityCheckKey = key(JmlOption.PURITYCHECK);
	/** The preference store key for the timeout option. */
	final static public String timeoutKey = key(JmlOption.TIMEOUT);
	/** The preference store key for the keys option. */
	final static public String optionalKeysKey = prefix + "optionalKeys"; //$NON-NLS-1$
	/** The preference store key for the showNotImplemented option. */
	final static public String showNotImplementedKey = key(JmlOption.SHOW_NOT_IMPLEMENTED);
	/** The preference store key for the showNotExecutable option. */
	final static public String showNotExecutableKey = key(JmlOption.SHOW_NOT_EXECUTABLE);
	/** The preference store key for the noInternalSpecs option. */
	final static public String useInternalSpecsKey = key(JmlOption.INTERNALSPECS);
	/** The preference store key for the noInternalRuntime option. */
	final static public String useInternalRuntimeKey = key(JmlOption.INTERNALRUNTIME);
	/** The preference store key for the list of other options */
	final static public String otherOptionsKey = prefix + "otherOptions"; //$NON-NLS-1$

	/** RAC option that says to use Java asserts when compiling assertions */
	final static public String compileToJavaAssert = key(JmlOption.RAC_COMPILE_TO_JAVA_ASSERT);
	/** RAC option that skips checking Java features such as Null Pointer Exceptions, letting Java issue its own exception */
	final static public String racCheckJavaFeatures = key(JmlOption.RAC_JAVA_CHECKS);
	/** RAC option that disables checking assumptions */
	final static public String racCheckAssumptions = key(JmlOption.RAC_CHECK_ASSUMPTIONS);
	/** RAC option that distinguishes internal and entry precondition errors */
	final static public String racPreconditionEntry = key(JmlOption.RAC_PRECONDITION_ENTRY);
	/** RAC option which disables including source code in compiled-in error messages */
	final static public String racShowSource = key(JmlOption.RAC_SHOW_SOURCE);

	/** If enabled, ESC is performed automatically upon an Eclipse build */
	final static public String enableESCKey = prefix + "enableESC"; //$NON-NLS-1$
	/** If enabled, RAC is performed automatically upon an Eclipse build */
	final static public String enableRacKey = prefix + "enableRac"; //$NON-NLS-1$
	
	/** The preference store key for the racbin option */
	final static public String racbinKey = prefix + "racbin"; //$NON-NLS-1$
	
	/** The prefix used for prover executable path preferences - this must be
	 * the same as the prefix used in the properties file.
	 */
	final static public String proverPrefix = Strings.proverPropertyPrefix;

	/** A preference that contains the names of solvers to be shown in the preference page. */
	final static public String solversKey = prefix + "solvers"; //$NON-NLS-1$
	
	// FIXME - change this
	final static public String defaultProverKey = Strings.defaultProverProperty;
	
	// Job Control preferences (no corresponding JmlOption option)
	final static public String jobQueuesKey = key("jobQueues");
	final static public String jobStrategyKey = key("jobStrategy");
	
}