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
import org.jmlspecs.openjml.IOption;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.Strings;

import com.sun.tools.javac.util.Context;

/**
 * This class manages user-settable options for OpenJML - at least those supported by the plug-in. Note that the plug-in uses the usual Eclipse preference store to persist values of options. The key
 * used for preferences is the same as the key used to specify the option in an openjml.properties file or in a -D command-line option. It consists of a prefix followed by the name of the option as it
 * is specified on the command-line (without the - sign).
 * <P>
 * The OpenJML application itself reads openjml.properties files to read user-set preferences; a plug-in reads the values stored in the preferencesStore. Consequently, the Preferences page of the
 * plug-in has a button to read in any openjml.properties files.
 *
 */
public class Options {

    /**
     * Returns the value of a Boolean-valued option from the preferences store; a non-existent value is returned as false.
     */
    static public boolean isOption(String key) {
        Boolean value = Activator.getDefault().getPreferenceStore().getBoolean(key);
        return value != null && value;
    }

    /** Sets the value of a Boolean-valued option in the preferences store. */
    static public void setOption(String key, boolean value) {
        Activator.getDefault().getPreferenceStore().setValue(key, value);
    }

    /**
     * Returns the value of a String-valued option from the preferences store; a non-existent preference will return null.
     */
    static String value(String key) {
        return Activator.getDefault().getPreferenceStore().getString(key);
    }

    /** Sets the value of a String-valued option in the preferences store. */
    static void setValue(String key, String value) {
        Activator.getDefault().getPreferenceStore().setValue(key, value);
    }

    /** Cached value of the verboseness */
    static public boolean uiverboseness = false;

    /** Caches values of properties as needed, based on preference store */
    public static void cache() {
        Options.uiverboseness = Options.isOption(Options.uiverbosityKey);
    }

    /** Iterates over all the preferences declared in this class (by reflection),
     * 
     */
    
    /** Sets each known preference (the keys declared in this file, iterating using reflection)
     * to its default value (in the preferences store).
     */
    // TODO: NOT USED
    public void setStoreToDefaults() {
        IPreferenceStore store = Activator.getDefault().getPreferenceStore();
        for (Field f : Options.class.getDeclaredFields()) {
            String fieldName = f.getName();
            if (fieldName.endsWith("Key")) {
                try {
                    // All keys are Strings
                    // The value of the field is a preference key
                    String key = f.get(null).toString(); // value of the field
                    store.setToDefault(key);
                } catch (IllegalAccessException e) {
                    // Should never happen
                }
            }
        }
    }

    // TODO: Should the preferences be completely set to defaults first?
    /** Initializes preference store from properties and JmlOptions,
     * if current option values so indicate; called during Activator.start */
    public static void initialize() {
        IPreferenceStore store = Activator.getDefault().getPreferenceStore();
        store.setDefault(Options.showJobControlDialogKey, true);
        boolean b = store.getBoolean(Options.alreadyInitializedKey);
        boolean bb = store.getBoolean(Options.initializeOnStartupKey);
        if (!b || bb) {
            Properties properties = org.jmlspecs.openjml.Utils.findProperties(null);
            for (java.util.Map.Entry<Object, Object> entry : properties.entrySet()) {
                String key = entry.getKey().toString();
                String value = entry.getValue().toString();
                if (key.startsWith(Strings.optionPropertyPrefix)) {
                    boolean isBoolean = false;
                    String optname = "-" + key.substring(Strings.optionPropertyPrefix.length());
                    for (IOption o : JmlOption.list) { // FIXME - change to a lookup
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
            store.setValue(Options.alreadyInitializedKey, true);
        }
        Options.cache();
    }

    /** The preference key for a JmlOption */
    public static String key(JmlOption opt) {
        return prefix + opt.optionName().substring(1);
    }

    /** The preference key for a non-JmlOption */
    public static String key(String s) {
        return prefix + s;
    }

    // Note: The values of the keys must correspond to the names of the
    // command-line options. 
    
    // Also the names of the fields that represent preference keys corresponding to
    // must end with 'Key'. Those that do are loaded automatically.

    /** The prefix to be put on each key that is a command-line option for the application. */
    final static public String prefix = Strings.optionPropertyPrefix;

    // These first ones are GUI-specific options

    /** A fake preference store key for the update button. */
    final static public String updateKey = key("update"); //$NON-NLS-1$

    final static public String alreadyInitializedKey = key("alreadyInitialized");
    /** The preference store key for the initialize on startup button */
    final static public String initializeOnStartupKey = key("initializeOnStartup");

    /** The preference store key for the Java verbosity (boolean). */
    final static public String javaverboseKey = key("verbose"); //$NON-NLS-1$
    /** The preference store key for the verbosity (quiet, nowarnings, verbose) option. */
    final static public String verbosityKey = key("verboseness"); //$NON-NLS-1$
    /** The preference store key for the uiverbosity option. */
    final static public String uiverbosityKey = key("uiverbosity"); //$NON-NLS-1$
    /** The preference store key for the show-error-popups UI control. */
    final static public String showErrorPopupsKey = key("showErrorPopups"); //$NON-NLS-1$

    /** If enabled, ESC is performed automatically upon an Eclipse build */
    final static public String enableESCKey = key("enableESC"); //$NON-NLS-1$
    /** If enabled, RAC is performed automatically upon an Eclipse build */
    final static public String enableRacKey = key("enableRac"); //$NON-NLS-1$

    /** The preference store key for the racbin option */
    final static public String racbinKey = key("racbin"); //$NON-NLS-1$

    /** The preference store key for the keys option. */
    final static public String optionalKeysKey = key("optionalKeys"); //$NON-NLS-1$

    /** The preference store key for the list of other options */
    final static public String otherOptionsKey = key("otherOptions"); //$NON-NLS-1$

    // The next set correspond to OpenJML options

    /** The preference store key for the checkSpecsPath option. */
    final static public String checkSpecsPathKey = key(JmlOption.CHECKSPECSPATH);
    /** The preference store key for the nonnullByDefault option. */
    final static public String nullableByDefaultKey = key(JmlOption.NULLABLEBYDEFAULT);
    /** The preference store key for the -show option. */
    final static public String showKey = key(JmlOption.SHOW);
    /** The preference store key for the -checkFeasibility option. */
    final static public String feasibilityKey = key(JmlOption.FEASIBILITY);

    // /** The preference store key for the show trace info option. */
    // final static public String traceKey = prefix + "trace"; //$NON-NLS-1$
    // /** The preference store key for the -subexpressions option. */
    // final static public String subexpressionsKey = prefix + "subexpressions"; //$NON-NLS-1$
    /** The preference store key for the max esc warnings option. */
    final static public String escMaxWarningsKey = key(JmlOption.ESC_MAX_WARNINGS);
    /** The preference store key for the strict JML option. */
    final static public String strictKey = key(JmlOption.LANG);
    /** The preference store key for the check purity option. */
    final static public String purityCheckKey = key(JmlOption.PURITYCHECK);
    /** The preference store key for the timeout option. */
    final static public String timeoutKey = key(JmlOption.TIMEOUT);
    /** The preference store key for the showNotImplemented option. */
    final static public String showNotImplementedKey = key(JmlOption.SHOW_NOT_IMPLEMENTED);
    /** The preference store key for the showNotExecutable option. */
    final static public String showNotExecutableKey = key(JmlOption.SHOW_NOT_EXECUTABLE);
    /** The preference store key for the noInternalSpecs option. */
    final static public String useInternalSpecsKey = key(JmlOption.INTERNALSPECS);
    /** The preference store key for the noInternalRuntime option. */
    final static public String useInternalRuntimeKey = key(JmlOption.INTERNALRUNTIME);

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

    /**
     * The prefix used for prover executable path preferences - this must be the same as the prefix used in the properties file.
     */
    final static public String proverPrefix = Strings.proverPropertyPrefix;

    /** A preference that contains the names of solvers to be shown in the preference page. */
    final static public String solversKey = key("solvers"); //$NON-NLS-1$

    // FIXME - change this
    final static public String defaultProverKey = Strings.defaultProverProperty;

    // Job Control preferences (no corresponding JmlOption option)
    final static public String alwaysSaveJobControlDialogKey = key("alwaysSaveJobControlDialog");
    final static public String showJobControlDialogKey = key("showJobControlDialog");
    final static public String jobQueuesKey = key("jobQueues");
    final static public String jobStrategyKey = key("jobStrategy");

    // Specification inference options

    final static public String inferDebug = key("inferDebug"); //$NON-NLS-1$
    final static public String inferTimeout = key("infertimeout"); //$NON-NLS-1$
    final static public String inferPersistSpecsTo = key("inferPersistSpecs"); //$NON-NLS-1$
    final static public String inferMaxDepth = key("inferMaxDepth"); //$NON-NLS-1$
    final static public String inferDevTools = key("inferDevTools"); //$NON-NLS-1$
    final static public String inferDefaultPrecondition = key("inferDefaultPrecondition"); //$NON-NLS-1$

    // TODO: Check that all of the options are used
    // TODO: The inference keys do not ed with 'Key'
}
