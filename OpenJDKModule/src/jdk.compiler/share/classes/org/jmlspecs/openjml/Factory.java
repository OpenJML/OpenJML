package org.jmlspecs.openjml;

import java.io.PrintWriter;

import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;

import com.sun.tools.javac.util.Options;

/** This class is a top-level factory for API objects. */
public class Factory {
    
    /** The interface to be implemented by new API factories */
    public interface IAPIFactory {
    	/** Creates a new API object
    	 * @param w destination of non-diagnostic output (null means System.out)
         * @param listener destination of diagnostic output (null means use the writer)
         * @param args command-line options
    	 */
    	@NonNull IAPI makeAPI(@Nullable PrintWriter w, @Nullable DiagnosticListener<JavaFileObject> listener, @Nullable Options options, String... args) throws Exception;
    }
    
    /** The default concrete API factory class */
    public static class APIFactory implements IAPIFactory {
    	/** Creates a new API object
    	 * @param w destination of non-diagnostic output (null means System.out)
         * @param listener destination of diagnostic output (null means use the writer)
         * @param args command-line options
    	 */
        public @NonNull IAPI makeAPI(@Nullable PrintWriter w, @Nullable DiagnosticListener<JavaFileObject> listener, @Nullable Options options, String... args) throws Exception {
            return new API(w,listener,options,args);
        }
    }
    
    /** The factory to use to generated API objects. */
    public static @NonNull IAPIFactory apiFactory = new Factory.APIFactory();
    
    /** Creates a new IAPI object using the registered factory.
     * @param args command-line options
     */
    static public @NonNull IAPI makeAPI(String ... args) throws Exception {
        return apiFactory.makeAPI(null,null,null,args);
    }

    /** Creates a new IAPI object using the registered factory.
     * @param w destination of non-diagnostic output (null means System.out)
     * @param listener destination of diagnostic output (null means use the writer)
     * @param args command-line options
     */
    static public @NonNull IAPI makeAPI(@Nullable PrintWriter w, @Nullable DiagnosticListener<JavaFileObject> listener, @Nullable Options options, String... args) throws Exception {
        return apiFactory.makeAPI(w,listener,options,args);
    }



}