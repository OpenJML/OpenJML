/*
 * Copyright (c) 2006-2011 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.PrintWriter;
import java.io.StringWriter;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;

/** The logging mechanism for the OpenJML plugin - used for reporting progress or
 * errors within the plugin itself (i.e. not messages arising from the use of
 * command-line OpenJML nor messages from analysis of user code).  All textual user output is sent to
 * the static methods of this class; specific kinds of reporters register as listeners.
 * Actually - in the current implementation there can be only one listener.
 * @author David R. Cok
 */

// FIXME - There is also an Eclipse plugin log mechanism - should we be using
// that directly? Currently this Log sends material to the console log and 
// some material to the plugin log. The alternative is to send everything to 
// the Eclipse provided log and have the ConsoleLog be a listener.
public class Log {

	/** The singleton Log object that does the actual logging */
	public static final /*@ non_null*/ Log log = new Log();

	/** Call this method for any non-error output - it sends the message on to the 
	 * current listeners, or to System.out if there are no listeners
	 * @param message the message to write; a new line will be added
	 */
	static public void log(/*@ non_null*/String message) { 
		if (log.listener != null) log.listener.log(message);
		else System.out.println(message); 
	}

	/** Call this method for any error output that happens because of an
	 * exception - it sends a message to the 
	 * current listeners, or to System.out if there are no listeners
	 * @param message the message to write; a new line will be added
	 */
	static public void errorlog(/*@ non_null*/String message, /*@ nullable */Throwable e) {
		String emsg = e == null ? null : e.getMessage();
		if (emsg != null && !emsg.isEmpty()) message = message + " (" + emsg + ")";
		if (e != null) {
			StringWriter sw = new StringWriter();
			PrintWriter pw = new PrintWriter(sw);
			pw.println();
			e.printStackTrace(pw);
			message = message + Env.eol + sw.toString(); 
		}
		if (log.listener != null) log.listener.log(message);
		else System.out.println(message); 
	}

	/** The interface expected of listeners */ 
	public static interface IListener {
		public void log(String msg);
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

	/** A class that listens to diagnostic messages coming in from OpenJDK
	 * and reports them into the OpenJML logging mechanism for Log listeners
	 * to hear. 
	 */
	final static public class UIListener<S> implements DiagnosticListener<S> {
		public UIListener() {
		}

		@Override 
		public void report(Diagnostic<? extends S> diagnostic) {
			Log.log(diagnostic.toString());
		}
	}
}
