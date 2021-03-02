package org.jmlspecs.utils;

public class Utils {

	public static final String RUNTIME = "org.jmlspecs.runtime";
    public static final String ASSERTION_FAILURE = "assertionFailureL"; // Must match the method name
    public static final String ASSERTION_FAILURE_EX = "assertionFailureE"; // Must match the method name
    public static final String REPORT_EXCEPTION = "reportException"; // must match method name

    /** Determines whether to report assertion failures as exceptions (true)
     * or error messages (false).
     */
    public static boolean useExceptions = System.getProperty("org.jmlspecs.openjml.racexceptions") != null;
    
    /** Determines whether to report assertion failures as java assertions (true)
     * or error messages (false).
     */
    public static boolean useJavaAssert = System.getProperty("org.jmlspecs.openjml.racjavaassert") != null;
    
    /** If true, then error messages reporting assertion failures are 
     * accompanied with a stack trace to log.errorWriter.
     */
    public static boolean showStack = System.getProperty("org.jmlspecs.openjml.racshowstack") != null;
    
    // FIXME - what are these for - are they used?
    static final public String invariantMethodString = "_JML$$$checkInvariant";
    static final public String staticinvariantMethodString = "_JML$$$checkStaticInvariant";

}
