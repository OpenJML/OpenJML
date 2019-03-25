/*
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.ResourceBundle;

import org.eclipse.osgi.util.NLS;

/** The logging mechanism for the OpenJML plugin - used for reporting progress or
 * errors within the plugin itself (i.e. not messages arising from the use of
 * command-line OpenJML nor messages from analysis of user code).  All textual 
 * user output is sent to
 * the static methods of this class; specific kinds of reporters register as listeners.
 * Actually - in the current implementation there can be only one listener.
 * If no listener is present, the message will be sent to System.out.
 * @author David R. Cok
 */

// TODO - There is also an Eclipse plugin log mechanism - should we be using
// that directly? Currently this Log sends material to the console log.
// The alternative is to send everything to 
// the Eclipse provided log and have the ConsoleLog be a listener.
public class Log {

    /** This reads the property file containing the error message format 
     * strings for the OpenJML UI.
     */
    public static final ResourceBundle errorBundle = ResourceBundle.getBundle("org.jmlspecs.openjml.eclipse.errors"); //$NON-NLS-1$

    /** The singleton Log object that does the actual logging */
    public static final /*@ non_null*/ Log log = new Log();

    /** Call this method for any non-error output - it sends the message on to the 
     * current listeners, or to System.out if there are no listeners
     * @param message the message to write; a new line will be added
     */
    static public void log(/*@ non_null*/String message) { 
        log.collected.add(message);
        if (log.listener != null) log.listener.log(message);
        else System.out.println(message); 
    }

    /** Call this method for any error output - it sends a message to the 
     * current listeners, or to System.out if there are no listeners;
     * if an exception is given, the stack trace is output as well.
     * @param message the message to write; a new line will be added
     */
    static public void errorlog(/*@ non_null*/String message, /*@ nullable */Throwable e) {
        String emsg = e == null ? null : e.getMessage();
        if (emsg != null && !emsg.isEmpty()) message = message + " (" + emsg + ")"; //$NON-NLS-1$ //$NON-NLS-2$
        if (e != null) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            pw.println();
            e.printStackTrace(pw);
            message = message + Env.eol + sw.toString(); 
        }
        log.collected.add(message);
        if (log.listener != null) log.listener.log(message);
        else System.out.println(message); 
    }

    /** Equivalent to errorlog except that the first argument is a localization
     * format string with placeholders ({0}, {1}, etc.) for the arguments;
     * the optional exception is handled as in errorlog.
     */
    static public void errorFormat(String format, /*@ nullable */Throwable e, Object...  args) {
        errorlog(NLS.bind(format, args), e);
    }

    /** Equivalent to errorlog except that the first argument is a localization
     * key string whose value is looked up in the .properties file;
     * the optional exception is handled as in errorlog.
     */
    static public void errorKey(String key, /*@ nullable */Throwable e, Object...  args) {
        String format = errorBundle.getString(key);
        errorlog(NLS.bind(format, args), e);
    }

    /** The interface expected of listeners */ 
    public static interface IListener {
        /** Called by the application for any message logged (including errors) */
        public void log(String msg);
        /** The OutputStream corresponding to the listener. */
        public OutputStream getStream();
    }

    /** The one (if any) registered listener */
    private /*@ nullable */IListener listener = null;

    /** Call this to get the current listener */
    public IListener listener() {
        return listener;
    }

    /** Call this to set the current listener */
    public void setListener(/*@ nullable */IListener l) {
        listener = l;
    }

    private java.util.List<String> collected = new LinkedList<String>();

    public static java.util.List<String> collect(boolean clear) {
        java.util.List<String> result = new ArrayList<String>(log.collected);
        if (clear) log.collected.clear();
        return result;
    }

}
