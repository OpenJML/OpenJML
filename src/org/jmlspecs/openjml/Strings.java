/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

/** This class holds (almost) all explicit strings or other constant data used in OpenJML,
 * particularly that data that is customer visible. */
public class Strings {

    // All explicit strings should be here
    
    // The following are stored here globally (e.g., for all compilation
    // contexts). I expect they will always be constant, but one could, for
    // example, reset them by a command-line option. No guarantees on the
    // behavior of the tool if these are changed during processing.  They are
    // final for now - which could be changed if necessary.
 
    // Names of Java options
    static public final String classpathOptionName = "-classpath";
    static public final String sourcepathOptionName = "-sourcepath";


    /** The default application name */
    static public final String applicationName = "openjml";
    
    /** A string giving the name of the package that JML annotations are in.
     */
    static public final String jmlAnnotationPackage = "org.jmlspecs.annotation";

    /** The fully-qualified name of the NonNull annotation */
    static public final String nonnullAnnotation = jmlAnnotationPackage + ".NonNull";
    
    /** The fully-qualified name of the Nullable annotation */
    static public final String nullableAnnotation = jmlAnnotationPackage + ".Nullable";
    
    /** The fully-qualified name of the Helper annotation */
    static public final String helperAnnotation = jmlAnnotationPackage + ".Helper";
    
    /** The fully-qualified name of the Pure annotation */
    static public final String pureAnnotation = jmlAnnotationPackage + ".Pure";
    
    /** The fully-qualified name of the Model annotation */
    static public final String modelAnnotation = jmlAnnotationPackage + ".Model";
    
    /** The name of the jar file that constitutes an openjml release. */
    static public final String releaseJar = "openjml.jar";
    
    /** The name of the jar file that contains a copy of the specs to use, as part of
     * a release.  This is expected to be the specs for the version of Java 
     * being used.  
     */
    static public final String specsJar = "jmlspecs.jar";
    
    /** The name of the OpenJML runtime library. */
    static public final String runtimeJarName = "jmlruntime.jar";

    static public final String SIMPLIFY = "simplify";
    
    /** The expected name of the OpenJML properties file. */
    static public final String propertiesFileName = "openjml.properties";
    
    
    /** This string is the fully-qualified name of the JML compiler messages file 
     * (without the .properties suffix). */
    static public final String messagesJML = "org.jmlspecs.openjml.messages";
    
    /** This array gives the suffixes recognized as JML specification files, in order of priority */
    /*@ non_null*/
    static public final String[] suffixes = { ".jml", ".java" };
    
    /** This gives the character that marks a mock directory (cf. JmlSpecs), mostly for use in testing */
    // FIXME - not yet used everywhere it should be
    static public final char mockDirChar = '$';
    
    /** A property name prefix for adding new options or specifying values */
    static public final String optionPropertyPrefix = "openjml.option.";
    
    /** A property name prefix for specifying information about provers */
    static public final String proverPropertyPrefix = "openjml.prover.";
    
    /** The property name to specify a default prover */
    static public final String defaultProverProperty = "openjml.defaultProver";
    
    /** A Java property name used to indicate the directory path on which to find specification files */
    public static final String specsPathEnvironmentPropertyName = "org.jmlspecs.specspath";

    /** A Java property name giving the directory in which specifications for the Java system libraries are found */
    public static final String systemSpecsLocationEnvironmentPropertyName = "org.jmlspecs.system.specs";
    
    /** Set this to the name of a Java property that contains the default
     * runtime classpath. 
     */
    // FIXME - clarify the use of this
    public static final String defaultRuntimeClassPath = "openjml.defaultRuntimeClassPath";

    /** Set this to the name of a Java property that contains the location of 
     * the project files in Eclipse, so that testing proceeds OK. 
     * If this directory is null or does not exist, it is ignored and tests will fail.
     * Only used in testing within Eclipse.
     */
    public static final String eclipseProjectLocation = "openjml.eclipseProjectLocation";

    /** Set this to the name of a Java property that contains the location of 
     * the project files in Eclipse, so that testing proceeds OK. 
     * If this directory is null or does not exist, it is ignored and tests will fail.
     * Only used in testing within Eclipse.
     */
    public static final String eclipseSpecsProjectLocation = "openjml.eclipseSpecsProjectLocation";
    

}
