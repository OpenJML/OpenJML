/**
 * Copyright (c) 2005 David R. Cok.
 *
 * @author David R. Cok
 * Jun 18, 2005 
 * 
 */
package org.jmlspecs.openjml.eclipse;



/**
 * This class holds options that control the global behavior
 * of the application.  If you add a new option, then you should
 * also (a) add code in setDefaults() to provide a default value,
 * (b) add code in CommandLineOptions to provide a way to set 
 * the option from the command line, (c) add code in AbstractPreferences
 * to create a way to persist the value of the option, and (d) add code
 * in Preferences to provide a way to set the option value from the UI.
 *
 */
public class Options {

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
  
  // Options relating to Java
  
  /** The classpath as set on the command-line, used to 
   *  search for and process files listed on the command-line.
   */
  //@ non_null
  public String classpath; // FIXME - change to an array of locations
  
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
  
  /** The name of the automatically created container for holding
   * links to the items of the specification path within the Eclipse
   * workspace.
   */
  public String specsProjectName;
  
  /** The set of locations of specifications. */
  public String specspath;  // FIXME - change to an array of locations
  
  /** If true, then annotations beginning with +@ are processed as well
   * as those beginning with @ or -@.
   */
  public boolean parsePlus;
  
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
  
  /** If true, check that elements of the specs path all exist.  If false, ignore
   * any non-existent directories or non-directories on the path.
   */
  public boolean checkSpecsPath;
  
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
    
    classpath = System.getProperty("java.classpath","");
    destination = "";
    source = "1.5";
    
    specsProjectName = Env.defaultSpecsProjectName;
    specspath = System.getenv("SPECSPATH");
    parsePlus = false;
    checkPurity = false;
    nonnullByDefault = true;
    checkSpecsPath = true;
    showNotImplemented = true;
    showNotExecutable = true;
    noInternalSpecs = false;
    noInternalRuntime = false;
    
    return this;
  }
}