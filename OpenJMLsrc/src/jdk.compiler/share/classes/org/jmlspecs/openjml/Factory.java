package org.openjml;

import java.io.PrintWriter;

import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;


import com.sun.tools.javac.util.Options;

/** This class is a top-level factory for API objects. */
public class Factory {
    
    private Factory() {}
    
    /** The interface to be implemented by new API factories */
    public static interface IAPIFactory {
    	/** Creates a new API object
    	 * @param w destination of non-diagnostic output (null means System.out)
         * @param listener destination of diagnostic output (null means use the writer)
         * @param args command-line options
    	 */
        @SuppressWarnings("exports")
    	/*@non_null*/ IAPI makeAPI(/*@nullable*/ PrintWriter w, /*@nullable*/ DiagnosticListener<JavaFileObject> listener, String[] args) throws Exception;
    }
    
    /** The default concrete API factory class */
    protected static class APIFactory implements IAPIFactory {
        
        public APIFactory() {}
        
    	/** Creates a new API object
    	 * @param w destination of non-diagnostic output (null means System.out)
         * @param listener destination of diagnostic output (null means use the writer)
         * @param args command-line options
    	 */
        @SuppressWarnings("exports")
        public /*@non_null*/ IAPI makeAPI(/*@nullable*/ PrintWriter w, /*@nullable*/ DiagnosticListener<JavaFileObject> listener, String[] args) throws Exception {
            return new API(w,w,listener);
        }
    }
    
    /** The factory to use to generated API objects. */
    public static /*@non_null*/ IAPIFactory apiFactory = new Factory.APIFactory();
    
    /** Creates a new IAPI object using the registered factory.
     * @param args command-line options
     */
    static public /*@non_null*/ IAPI makeAPI(String ... args) throws Exception {
        return apiFactory.makeAPI(null,null,args);
    }

    /** Creates a new IAPI object using the registered factory.
     * @param w destination of non-diagnostic output (null means System.out)
     * @param listener destination of diagnostic output (null means use the writer)
     * @param args command-line options
     */
    @SuppressWarnings("exports")
    static public /*@non_null*/ IAPI makeAPI(/*@nullable*/ PrintWriter w, /*@nullable*/ DiagnosticListener<JavaFileObject> listener, /*@nullable*/ Options options, String... args) throws Exception {
        return null; // apiFactory.makeAPI(w,listener,options,args);
    }



}