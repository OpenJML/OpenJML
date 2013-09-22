/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import com.sun.tools.javac.util.Name;

/** This class holds (almost) all explicit strings or other constant data used in OpenJML,
 * particularly that data that is customer visible. */
public class Strings {

    // All explicit strings should be here
    
    // The following are stored here globally (e.g., for all compilation
    // contexts). I expect they will always be constant, but one could, for
    // example, reset them by a command-line option. No guarantees on the
    // behavior of the tool if these are changed during processing.  They are
    // final for now - which could be changed if necessary.
 
	static public final String empty = ""; //$NON-NLS-1$
    static public final String underscore = "_"; //$NON-NLS-1$
    static public final String space = " "; //$NON-NLS-1$
    static public final String dot = "."; //$NON-NLS-1$
    static public final String eol = System.getProperty("line.separator");
	
    // Names of Java options
    static public final String classpathOptionName = com.sun.tools.javac.main.OptionName.CLASSPATH.optionName;
    static public final String sourcepathOptionName = com.sun.tools.javac.main.OptionName.SOURCEPATH.optionName;
    static public final String outputOptionName = com.sun.tools.javac.main.OptionName.D.optionName;

    static public final String javaSuffix = ".java"; //$NON-NLS-1$
    static public final String specsSuffix = ".jml"; //$NON-NLS-1$

    /** The default application name */
    static public final String applicationName = "openjml"; //$NON-NLS-1$
    
    /** The fully-qualified name of the runtime utilities class. */
    static public final String runtimeUtilsFQName = "org.jmlspecs.utils.Utils";
    
    /** A string giving the name of the package that default JML runtime classes are in.
     */
    static public final String jmlSpecsPackage = "org.jmlspecs.lang"; //$NON-NLS-1$
    
    /** A string giving the name of the package that JML annotations are in.
     */
    static public final String jmlAnnotationPackage = "org.jmlspecs.annotation"; //$NON-NLS-1$

    /** The fully-qualified name of the NonNull annotation */
    static public final String nonnullAnnotation = jmlAnnotationPackage + ".NonNull"; //$NON-NLS-1$
    
    /** The fully-qualified name of the Nullable annotation */
    static public final String nullableAnnotation = jmlAnnotationPackage + ".Nullable"; //$NON-NLS-1$
    
    /** The fully-qualified name of the Helper annotation */
    static public final String helperAnnotation = jmlAnnotationPackage + ".Helper"; //$NON-NLS-1$
    
    /** The fully-qualified name of the Pure annotation */
    static public final String pureAnnotation = jmlAnnotationPackage + ".Pure"; //$NON-NLS-1$
    
    /** The fully-qualified name of the Model annotation */
    static public final String modelAnnotation = jmlAnnotationPackage + ".Model"; //$NON-NLS-1$
    
    /** The name of the jar file that constitutes an openjml release. */
    static public final String releaseJar = "openjml.jar"; //$NON-NLS-1$
    
    /** The name of the jar file that contains a copy of the specs to use, as part of
     * a release.  This is expected to be the specs for the version of Java 
     * being used.  
     */
    static public final String specsJar = "jmlspecs.jar"; //$NON-NLS-1$
    
    /** The name of the OpenJML runtime library. */
    static public final String runtimeJarName = "jmlruntime.jar"; //$NON-NLS-1$

    static public final String SIMPLIFY = "simplify"; //$NON-NLS-1$
    
    /** The expected name of the OpenJML properties file. */
    static public final String propertiesFileName = "openjml.properties"; //$NON-NLS-1$
    
    
    /** This string is the fully-qualified name of the JML compiler messages file 
     * (without the .properties suffix). */
    static public final String messagesJML = "org.jmlspecs.openjml.messages"; //$NON-NLS-1$
    
    /** This array gives the suffixes recognized as JML specification files, in order of priority */
    /*@ non_null*/
    static public final String[] suffixes = { specsSuffix, javaSuffix };
    
    /** This gives the character that marks a mock directory (cf. JmlSpecs), mostly for use in testing */
    // FIXME - not yet used everywhere it should be
    static public final char mockDirChar = '$';
    
    /** A property name prefix for adding new options or specifying values */
    static public final String optionPropertyPrefix = "org.openjml.option."; //$NON-NLS-1$
    
    /** A property name prefix for adding new options or specifying values */
    static public final String javaOptionPropertyPrefix = "org.openjml.java.option."; //$NON-NLS-1$
    
    /** A property name prefix for specifying information about provers */
    static public final String proverPropertyPrefix = "openjml.prover."; //$NON-NLS-1$
    
    /** The property name to specify a default prover */
    static public final String defaultProverProperty = "openjml.defaultProver"; //$NON-NLS-1$
    
    /** A Java property name used to indicate the directory path on which to find specification files */
    public static final String specsPathEnvironmentPropertyName = "org.jmlspecs.specspath"; //$NON-NLS-1$

    /** A Java property name giving the directory in which specifications for the Java system libraries are found */
    public static final String systemSpecsLocationEnvironmentPropertyName = "org.jmlspecs.system.specs"; //$NON-NLS-1$
    
    /** Set this to the name of a Java property that contains the default
     * runtime classpath. 
     */
    public static final String defaultRuntimeClassPath = "openjml.defaultRuntimeClassPath"; //$NON-NLS-1$

    /** Set this to the name of a Java property that contains the location of 
     * the project files in Eclipse, so that testing proceeds OK. 
     * If this directory is null or does not exist, it is ignored and tests will fail.
     * Only used in testing within Eclipse.
     */
    public static final String eclipseProjectLocation = "openjml.eclipseProjectLocation"; //$NON-NLS-1$

    /** Set this to the name of a Java property that contains the location of 
     * the project files in Eclipse, so that testing proceeds OK. 
     * If this directory is null or does not exist, it is ignored and tests will fail.
     * Only used in testing within Eclipse.
     */
    public static final String eclipseSpecsProjectLocation = "openjml.eclipseSpecsProjectLocation"; //$NON-NLS-1$
    
    /** A String used as the root of a variable name that is a temporary
     * intermediate result in an expression evaluation.
     */
    final static public String tmpVarString = "_JML__tmp"; //$NON-NLS-1$
    
    /** A String used as the Java variable for \result, hopefully obfuscated
     * enough that no one will ever actually use a Java variable with this name.
     */
    final static public String resultVarString = "_JML___result"; //$NON-NLS-1$
    
    /** A String used as the root of a temporary variable to hold the
     * value of the result of a 'new' constructor call .
     */
    final static public String newObjectVarString = "_JML___NEWOBJECT_"; //$NON-NLS-1$
    
    /** A String used as the root of a temporary variable to hold the value of
     * the result of a new array call.
     */
    final static public String newArrayVarString = "_JML___NEWARRAY_"; //$NON-NLS-1$
    
    /** A String used as the root of a temporary variable to represent a 
     * JML label expression.
     */
    final static public String labelVarString = "LABEL_"; //$NON-NLS-1$

    /** The prefix for names of assertions that are to be specifically checked */
    final static public String assertPrefix =  "ASSERT_"; //$NON-NLS-1$

    /** The prefix for names of assumptions */
    final static public String assumePrefix =  "ASSUME_"; //$NON-NLS-1$

    /** TODO: ??? */
    final static public String prePrefix = "Pre_"; //$NON-NLS-1$
    
    /** The prefix of variables that hold the values of formals in the pre-state,
     * for use by postconditions.
     */
    final static public String formalPrefix = "PRE_";
    
    /** A String used as variable that records the location of the return or
     * throw statement marking the exit from a method.
     */
    final static public String terminationVarString = "_JML___termination"; //$NON-NLS-1$
    
    /** A String used as the Java variable for \exception, hopefully obfuscated
     * enough that no one will ever actually use a Java variable with this name.
     */
    final static public String exceptionVarString = "_JML___exception"; //$NON-NLS-1$
    
    /** A String used as the name of the exception variable when catching 
     * runtime exceptions that may happen while evaluating JML expressions
     * during RAC.
     */
    final static public String runtimeException = "_JML__runtimeException"; //$NON-NLS-1$
    
    /** A string used as the name of the exception variable for method calls
     * within the body of a method.
     */
    final static public String exceptionCallVarString = "_JML___exceptionCall"; //$NON-NLS-1$
    
    /** A string used as the ID of the Exception in a a signals clause that
     * does not actually have an ID present: signals (Exception) ...
     */ // FIXME - can we use the one above just as well?
    public final static String syntheticExceptionID = "_JML___syntheticExceptionID"; //$NON-NLS-1$
    
    /** The prefix of names used to record the result of a
     * conditional expression.
     */
    public final static String conditionalResult = "_JML__conditionalResult_";
    
    /** Synthetic methods are constructed to implement the combination of model
     * fields and represents clauses; the name of method is this prefix string
     * combined with name of the model field.
     */
    public final static String modelFieldMethodPrefix = "_JML$model$";
    
    /** Name used for the array of allocation ids */
    public final static String allocName = "_alloc__";
    
    /** Name used for the array of allocation state */
    public final static String isAllocName = "_isalloc__";
    
    /** Name used to represent the 'this' object for non-static methods */
    public final static String thisName = "THIS";
    
    
}
