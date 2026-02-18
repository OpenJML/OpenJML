/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.LinkedList;
import java.util.List;



/** This class is used as a collection point for all output.  The SMTLIB defines two output
 * streams - regular output and diagnostic output, normally assigned to standard out and stderr.
 * The SMT out stream contains all standard SMT-LIB responses (including errors);
 * the SMT diag stream is for user-defined debugging or other information.
 * 
 * @author David Cok
 *
 */
public class Log {
	
	/** Number of errors logged since last clear */
	public int numErrors = 0;
	
	/** Keeps a reference to smtConfig for this instance of the SMT tool*/
	/*@NonNull*/ private SMT.Configuration smtConfig;
	
	/** Constructs a Log based on the given configuration, adding a 
	 * StandardListener */
	public Log(SMT.Configuration smtConfig) {
		this.smtConfig = smtConfig;
		addListener(new StandardListener());
	}
	
	/** This is an interface to be implemented by any Object that wants to hear log
	 * messages; the Object must register itself by calling Log.addListener.
	 */
	public static interface IListener {
		/** Called when messages are logged to the normal output. */
		public void logOut(String msg);
		
		/** Called when a response is logged to the normal output (it is expected that a line termination will be added);
		 * the argument is converted to text using the defaultPrinter in the smt configuration. */
		public void logOut(/*@ReadOnly*/ IResponse result);
		
		/** Called when an error is being recorded on the normal output (it is expected that a line termination will be added) */
		public void logError(String msg);
		
		/** Called when an IError is being recorded on the normal output - the listener has the opportunity to record error location information as well */
		public void logError(/*@ReadOnly*/ IResponse.IError result);
		
		/** Called when a message is sent to the SMT-LIB diagnostic output (it is expected that a line termination will be added) */
		public void logDiag(String msg);
		
		/** The character sequence with which to start any log line */
		public void indent(String chars);
	}
	
	/** This class logs to the standard PrintStreams out and diag.  The class is not static so that it
	 * can see out and diag in the containing class; it needs to do this so that changes to out and diag 
	 * are reflected here as well.
	 */
	public class StandardListener implements IListener {
		protected String prompt = ""; // TODO _ I don't think prompt is being used anywhere - remove it
		
		@Override
		public void indent(String chars) {
			prompt = chars;
		}
		
		/** Writes the message to the 'out' PrintStream */
		@Override
		public void logOut(String msg) {
			out.print(msg);
		}
		
		/** Writes the given response to the out stream, adding line termination */
		@Override
		public void logOut(/*@ReadOnly*/ IResponse response) {
			out.println(smtConfig.defaultPrinter.toString(response));
		}

		/** Writes the message to the 'out' PrintStream, adding line termination */
		@Override
		public void logError(String msg) {
			out.println(msg);
		}
		
		/** Writes the offending text line, column location in that line, and the error message
		 * to the 'out' stream.
		 */
		@Override
		public void logError(/*@ReadOnly*/IResponse.IError result) {
			IPos pos = result.pos();
			if (pos != null && pos.source() != null && !smtConfig.noshow) {
				diag.println(locationIndication(pos,prompt,smtConfig));
				diag.flush();
			}
			// Print the actual response
			out.println(smtConfig.defaultPrinter.toString(result));
		}
		

		/** Writes the message to the diag stream */
		@Override
		public void logDiag(String msg) {
			diag.println(msg);
		}
		
	}
	
	/** The list of listeners to send log messages to */
	protected List<IListener> listeners = new LinkedList<IListener>();
	
	/** The stream used for regular output and error information (may be modified directly)*/
	public /*@NonNull*/ java.io.PrintStream out = System.out;
	
	/** The stream used for diagnostic log information (may be modified directly) */
	public /*@NonNull*/ java.io.PrintStream diag = System.err;

	/** Prints the argument on the regular output stream and to any listeners */
	public void logOut(/*@NonNull*/ IResponse r) {
		for (IListener listener: listeners) {
			listener.logOut(r);
		}
	}
	
	// FIXME - the two following calls do not differ - do the callers of the first actually expect line terminations added?
	
	/** Prints the argument on the regular output stream and to any listeners*/
	public void logOut(/*@NonNull*/ String message) {
		for (IListener listener: listeners) {
			listener.logOut(message);
		}
	}
	
	/** Prints the argument on the regular output stream with no newline, and to any listeners. */
	public void logOutNoln(/*@NonNull*/ String message) {
		for (IListener listener: listeners) {
			listener.logOut(message);
		}
	}

	/** Reports the error to any listeners, returning the input. */
	public IResponse.IError logError(/*@NonNull*//*@ReadOnly*/ IResponse.IError r) {
		numErrors++;
		for (IListener listener: listeners) {
			listener.logError(r);
		}
		return r;
	}
	
	/** Reports the error to any listeners. */
	public void logError(/*@NonNull*/String r) {
		numErrors++;
		for (IListener listener: listeners) {
			listener.logError(r);
		}
	}
	
	/** Prints the argument to any listeners (adds a line terminator). */
	public void logDiag(/*@NonNull*/ String message) {
		for (IListener listener: listeners) {
			listener.logDiag(message);
		}
	}
	
	/** Sends the call to any listeners. */
	public void indent(/*@NonNull*/ String prompt) {
		for (IListener listener: listeners) {
			listener.indent(prompt);
		}
	}
	
	/** Adds a listener */
	public void addListener(IListener listener) {
		listeners.add(listener);
	}
	
	/** Clears all listeners */
	public void clearListeners() {
		listeners.clear();
	}
	
	/** Removes a listener (found by using object equality ==)
	 * @param listener the listener to add
	 * @return true if the argument was in the list
	 */
	public boolean removeListener(IListener listener) {
		return listeners.remove(listener);
	}

	/** Creates a location indication string from the pos argument; the returned value
	 * does not have a final line termination.
	 * @param pos the position to indicate
	 * @param prompt the prompt with which to begin each line
	 * @param smtConfig the current configuration
	 * @return a canonical string representation of the location
	 */
	// FIXME - REVIEW AND DOCUMENT more detail on what is actually produced
	static public String locationIndication(IPos pos, String prompt, SMT.Configuration smtConfig) {
		int s = pos.charStart();
		int e = pos.charEnd();
		ISource source = pos.source();
		int b;
		StringBuilder sb = new StringBuilder();
		b = source.lineBeginning(s);
		String prefix = "";
		String suffix = "";
		int start = 0;
		// Print the text line
		if (!smtConfig.interactive) {
			String input = source.textLine(s);
			int len = input.length();
			if (s-b > 150) {
				prefix = "... ";
				start = 20 * ((s-b)/20 - 1);
			}
			if (len-start > 150) {
				len = start + 150;
				suffix = "...\n";
				if (e > b+len) e = b+len;
			}
			if (!prefix.isEmpty() || !suffix.isEmpty()) input = prefix + input.substring(start,len) + suffix;
				
			// input will have a line terminator
			sb.append(input);
		}
		// Show the location in the text line
		if (smtConfig.interactive && prompt != null) {
			int bb = 0;
			while (bb < prompt.length()) {
				char c = prompt.charAt(bb);
				sb.append(c == '\t' ? '\t' : ' ');
				bb++;
			}
		}
		sb.append(prefix);
		b += start;
		while (b < s) {
			char c = source.charAt(b);
			sb.append(c == '\t' ? '\t' : ' ');
			b++;
		}
		while (b++ < e) {
			sb.append('^');
		}
		return sb.toString();
	}

}
