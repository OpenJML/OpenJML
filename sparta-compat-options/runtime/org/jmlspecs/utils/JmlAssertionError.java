package org.jmlspecs.utils;

/** Error object that is thrown when any JML assertion failure is 
 * encountered (if exceptions are enabled using Utils.useExceptions)
 * @author David Cok
 */
public class JmlAssertionError extends java.lang.Error {
    private static final long serialVersionUID = 1L;
    
    /** The Label used to identify the kind of JML assertion. */
    public String jmlAssertionType;
    
    /** The constructor with an informational message string
     * @param s the reason for the failure
     */
    public JmlAssertionError(String s, String label) {
        super(s);
        jmlAssertionType = label;
    }
    
    public static class Precondition extends JmlAssertionError {
        private static final long serialVersionUID = 1L;

        /** The constructor with an informational message string
         * @param s the reason for the failure
         */
        public Precondition(String s, String label) {
            super(s,label);
        }

    }
}