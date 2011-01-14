/*
 * Copyright (c) 2006-2010 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;

/** The logging mechanism for the OpenJML plugin - used for reporting progress or
 * errors within the plugin itself (i.e. not messages arising from the use of
 * command-line OpenJML nor messages from analysis of user code).  All user output is sent to
 * the static methods of this class; specific kinds of reporters register as listeners.
 * Actually - in the current implementation there can be only one listener.
 * @author David R. Cok
 */
public class Log {

	/** The singleton Log object that does the actual logging */
	public static Log log = new Log();

	/** Call this method for any non-error output - it sends the message on to the 
	 * current listener, or to System.out if there are no listeners
	 * @param message the message to write; a new line will be added
	 */
	static public void log(String message) { 
		if (log.listener != null) log.listener.log(message);
		else System.out.println(message); 
	}

	/** Call this method for any error output that happens because of an
	 * exception - it sends it message to the 
	 * current listener, or to System.out if there are no listeners
	 * @param message the message to write; a new line will be added
	 */
	static public void errorlog(String message, Throwable e) { // FIXME - record the stack trace
		String emsg = e == null ? null : e.getMessage();
		if (emsg != null && !emsg.isEmpty()) message = message + " (" + emsg + ")";
		if (log.listener != null) log.listener.log(message);
		else System.out.println(message); 
	}

	/** The interface expected of listeners */ 
	public static interface IListener {
		public void log(String msg);
	}

	/** The one (if any) registered listener */
	public IListener listener = null;

	/** Call this to set the current listener */
	public void setListener(IListener l) {
		listener = l;
	}

	//context.put(DiagnosticListener.class, new UIListener<JavaFileObject>() );

	/** A class that listens to diagnostic messages coming in from OpenJDK
	 * and reports them into the OpenJML logging mechanism for Log listeners
	 * to hear. 
	 */
	final static public class UIListener<S> implements DiagnosticListener<S> {
		public UIListener() {
		}

		public void report(Diagnostic<? extends S> diagnostic) {
			Log.log(diagnostic.toString());
		}

	}

}
