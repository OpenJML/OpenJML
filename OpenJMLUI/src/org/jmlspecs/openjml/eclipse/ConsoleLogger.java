/*
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2004-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;

import org.eclipse.core.runtime.ILog;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.Status;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.ui.progress.UIJob;

/** This class provides a Log.IListener implementation that sends
 * text written through methods in Log to the Eclipse console.
 */
public class ConsoleLogger implements Log.IListener {

	public static final String jobName = "Console Logger";  //$NON-NLS-1$
	
	/** Creates a new ConsoleLogger utility object
	 * 
	 * @param consoleName The name of the console to be logged to, as it will 
	 * appear in the Eclipse UI
	 */
	//@ requires consoleName != null;
	//@ modifies this.*;
	//@ ensures this.consoleName == consoleName;
	public ConsoleLogger(/*@ non_null */ String consoleName) {
		this.consoleName = consoleName;
		Plugin plugin = Activator.getDefault();
		this.pluginLog = plugin.getLog();
		this.pluginID = plugin.getBundle().getSymbolicName();
	}

	// This model variable models the content of the material
	// sent to the log.
	//@ model public String content;

	/** The name of the console that this plugin writes to. */
	//@ constraint \not_modified(consoleName);
	//@ spec_public
	//@ non_null
	final private String consoleName;

	/** The ILog of the plugin that this ConsoleLogger object connects to */
	//@ constraint \not_modified(pluginLog);
	//@ invariant pluginLog != null;
	//@ spec_public
	final private ILog pluginLog;

	/** The id of the plugin using this log */
	//@ constraint \not_modified(plugiID);
	//@ invariant pluginID != null;
	//@ spec_public
	final private String pluginID;

	/** If true, then informational output is recorded in the
	 *  system log (in addition to the console); if false, then it is not.
	 */
	public boolean alsoLogInfo = false;

	/** Cached value of the stream to use to write to the console */
	private MessageConsoleStream stream = null;
	//@ private constraint \old(stream) != null ==> \not_modified(stream);

	/** Returns the output stream for the IListener interface. */
	@Override
	public OutputStream getStream() {
		return getConsoleStream();
	}


	/** Creates, if necessary, and returns an instance of
	 *  the stream to use to write to the console
	 * @return The stream value to use
	 */
	//@ ensures \result != null;
	public MessageConsoleStream getConsoleStream() {
		if (stream == null) {
			MessageConsole console = null;
			IConsoleManager consoleManager = ConsolePlugin.getDefault().getConsoleManager();
			IConsole[] existing = consoleManager.getConsoles();
			for (int i=0; i<existing.length; ++i) {
				if (existing[i].getName().equals(consoleName)) {
					console = (MessageConsole)existing[i];
					break;
				}
			}
			if (console == null) {
				console = new MessageConsole(consoleName,null);
				consoleManager.addConsoles(new IConsole[]{console});
			}
			stream = console.newMessageStream();
		}
		return stream;
	}

	/** Color to use for error messages */
	static final private Color errorColor = new Color(null,255,0,0);

	// In the implementations below we write to the console in the UI thread.
	// This ensures that messages to the user appear in an understandable 
	// order. If we are already in the UI thread we definitely do not want
	// to write a message in a new job, because that would not execute until
	// the current job is complete.
	// FIXME - Whoops - there seems to be some interaction with the progress monitor - figure this out
	boolean test = false;
	
	/**
	 * Records an informational message adding a newline
	 * @param msg The message to log
	 */
	//@ requires msg != null;
	//@ modifies content;
	@Override 
	public void log(final String msg) {

		if(test &&  Display.getDefault().getThread() != Thread.currentThread() ) {
			UIJob j = new UIJob(Display.getDefault(),jobName) {
				public IStatus runInUIThread(IProgressMonitor monitor) {
					getConsoleStream().println(msg);
					// Also write it to the log file, if requested.
					if (alsoLogInfo) {
						pluginLog.log(
								new Status(Status.INFO, 
										pluginID,
										Status.OK, msg, null));
					}
					return Status.OK_STATUS;
				}
			};
			// FIXME - does this need a scheduling rule?
			j.setUser(true);
			j.schedule();

		} else {
			getConsoleStream().println(msg);
			// Also write it to the log file, if requested.
			if (alsoLogInfo) {
				pluginLog.log(
						new Status(Status.INFO, 
								pluginID,
								Status.OK, msg, null));
			}
		}
	}

	/**
	 * Records an informational message without a terminating new line.
	 * If a message is written to the System log, it will be written as
	 * an individual message, despite the absence of a newline.
	 * @param msg The message to log
	 */
	//@ requires msg != null;
	//@ modifies content;
	public void log_noln(final String msg) {
		if (test && Display.getDefault().getThread() != Thread.currentThread() ) {
			UIJob j = new UIJob(Display.getDefault(),jobName) { 
				public IStatus runInUIThread(IProgressMonitor monitor) {
					getConsoleStream().print(msg);
					// Also write it to the log file, if requested.
					if (alsoLogInfo) {
						pluginLog.log(
								new Status(Status.INFO, 
										pluginID,
										Status.OK, msg, null));
					}
					return Status.OK_STATUS;
				}
			};
			// FIXME - does this need a scheduling rule?
			j.setUser(true);
			j.schedule();

		} else {
			getConsoleStream().print(msg);
			// Also write it to the log file, if requested.
			if (alsoLogInfo) {
				pluginLog.log(
						new Status(Status.INFO, 
								pluginID,
								Status.OK, msg, null));
			}
		}
	}

	// FIXME - change to logln, errorlogln?

	/**
	 * Records an error message; only call this from the UI thread (because it 
	 * changes the color associated with the console).
	 * @param msg The message to log (adding a newline)
	 * @param e An associated exception (may be null)
	 */
	//@ modifies content;
	public void errorlog(final /*@ non_null */String msg, final /*@ nullable */ Throwable e) {
		if (test && Display.getDefault().getThread() != Thread.currentThread() ) {
			UIJob j = new UIJob(Display.getDefault(),jobName) {
				public IStatus runInUIThread(IProgressMonitor monitor) {
					// Always put errors in the log
					pluginLog.log(
							new Status(Status.ERROR, 
									pluginID,
									Status.OK, msg, e));
					MessageConsoleStream cs = getConsoleStream();
					Color c = cs.getColor();
					cs.setColor(errorColor);
					cs.println(msg);
					if (e != null) {
						PrintStream p = new PrintStream(cs);
						e.printStackTrace(p);
						p.flush();
					}
					try { cs.flush(); } catch (Exception ee) {} // ignore
					cs.setColor(c);
					return Status.OK_STATUS;
				}
			};
			// FIXME - does this need a scheduling rule?
			j.setUser(true);
			j.schedule();

		} else {
			// Always put errors in the log
			pluginLog.log(
					new Status(Status.ERROR, 
							pluginID,
							Status.OK, msg, e));
			MessageConsoleStream cs = getConsoleStream();
			Color c = cs.getColor();
			cs.setColor(errorColor);
			cs.println(msg);
			if (e != null) {
				PrintStream p = new PrintStream(cs);
				e.printStackTrace(p);
				p.flush();
			}
			try { cs.flush(); } catch (Exception ee) {} // ignore
			cs.setColor(c);
		}
	}

	/** Flushes the console stream */
	public void flush() throws IOException {
		getConsoleStream().flush();
	}

}

