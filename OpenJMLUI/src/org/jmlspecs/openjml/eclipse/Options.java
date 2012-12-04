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
		return System.getProperty(key) != null;
	}
	
	/** The prefix to be put on each key. */
	final static public String javaprefix = Strings.javaOptionPropertyPrefix;
	/** The prefix to be put on each key. */
	final static public String prefix = Strings.optionPropertyPrefix;

	/** A fake preference store key for the update button. */
	final static public String updateKey = prefix + "update";

//	/** The preference store key for the jmldebug option. */
//	final static public String debugKey = prefix + "debug";
	/** The preference store key for the checkSpecsPath option. */
	final static public String checkSpecsPathKey = prefix + "checkSpecsPath";
	/** The preference store key for the nonnullByDefault option. */
	final static public String nonnullByDefaultKey = prefix + "nonnullByDefault";
//	/** The preference store key for JML verbosity option. */
//	final static public String jmlverbosityKey = prefix + "jmlverbosity";
	/** The preference store key for the Java verbosity (boolean). */
	final static public String javaverboseKey = prefix + "verbose";
	/** The preference store key for the verbosity (quiet, nowarnings, verbose) option. */
	final static public String verbosityKey = prefix + "uiverbose";
	/** The preference store key for the uiverbosity option. */
//	final static public String uiverbosityKey = prefix + "uiverbosity";
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

    // Options relating to Eclipse or generic running of the tools

    /**
     * When true, debugging output is enabled
     */
    public boolean debug;

    /**
     * When 0, only error messages are emitted; 
     * When 1, warning and error messages are emitted;
     * When 2, a small amount of informational messages are emitted as well as warning/error messages;
     * When 3 or higher, verbose progress output is produced.
     */
    public int verbosity;
    
    
    /** Verbosity of the plugin itself:
     * When 0, quiet; 
     * When 1, timing and limited progress messages;
     * When 2, action information and replication of ESC warnings;
     * When 3 or higher, debug output.
     */
    public int uiverbosity = 1;

    // Options relating to Java

    /** The classpath as set on the command-line, used to 
     *  search for and process files listed on the command-line.
     */
    //@ non_null
    public String classpath; // FIXME - change to an array of locations; why is this needed in Options?

    /** The directory in which to place output .class files.
     * FIXME - is there reasonable default behavior when null?
     * (eclipse does not do the Java behavior of placing class files with
     * the java files, if there is more than one root directory)
     */
    public String destination;

    /** The level of Java source that is recognized; should be either
     * 1.4, 1.5, 1.6, 1.7.
     */
    public String source;

    // Options relating to JML

    /** Verbose output about JML */
    public boolean jmlverbose;
    
    /** If true, then annotations beginning with +@ are processed as well
     * as those beginning with @ or -@.
     */
    public boolean parsePlus; // FIXME - obsolete

    /** If true, checks for proper use of purity are performed. */
    public boolean checkPurity;

    /** If true, the project is NonNull by default; if false is Nullable by default. */
    public boolean nonnullByDefault;

    /** If true, warnings are issued for features used but not implemented. */
    public boolean showNotImplemented;

    /** If true, warnings are issued for features used in RAC but not executable. */
    public boolean showNotExecutable;

    /** If true, the internal library specifications are not automatically used. */
    public boolean noInternalSpecs;

    /** If true, the internal runtime library is not automatically used. */
    public boolean noInternalRuntime;

    /** If true (the default), the internal runtime library is automatically added
     * to the project classpath (so that the project files have the annotations defined).
     */
    public boolean autoAddRuntimeToProject;
    
    /** If true, warn if elements of the specs path do not exist.  If false, ignore
     * any non-existent directories or non-directories on the path.
     */
    public boolean checkSpecsPath;
    
    /** The directory (subdirectory of the project) in which RAC-compiled
     * class files are placed.
     */
    public String racbin;

    /** Creates an option structure with default settings. */
    public Options() { setDefaults(); }

    /**
     * Sets each field to its default.  Note that there may be
     * non-constant (e.g. environment dependent) options.
     * @return a reference to this, for convenience
     */
    public Options setDefaults() {
        debug = false;
        verbosity = 2;
        uiverbosity = 1;
        jmlverbose = false;
        
        classpath = System.getProperty("java.classpath","");  // FIXME Is this the right default for the classpath
        destination = "";
        source = "1.5";

        autoAddRuntimeToProject = true;
        parsePlus = false;
        checkPurity = false;
        nonnullByDefault = true;
        checkSpecsPath = true;
        showNotImplemented = true;
        showNotExecutable = true;
        noInternalSpecs = false;
        noInternalRuntime = false;
        racbin = "bin";

        return this;
    }
    // FIXME - other options?
}