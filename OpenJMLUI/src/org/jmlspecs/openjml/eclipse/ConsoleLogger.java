/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Aug 26, 2004
 */
package org.jmlspecs.openjml.eclipse;

import java.io.IOException;
import java.io.PrintStream;

import org.eclipse.core.runtime.ILog;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.Status;
import org.eclipse.swt.graphics.Color;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

/** This class provides Log.IListener implementation that sends
 * text written through methods in Log to the Eclipse console.
 */
public class ConsoleLogger implements Log.IListener {

  /** Creates a new ConsoleLogger utility object
   * 
   * @param consoleName The name of the console to be logged to
   */
  //@ requires consoleName != null;
  //@ requires plugin != null;
  //@ modifies \nothing;
  //@ ensures \result.consoleName == consoleName;
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
  private ILog pluginLog;

  /** The id of the plugin using this log */
  //@ constraint \not_modified(plugiID);
  //@ invariant pluginID != null;
  //@ spec_public
  private String pluginID;

  /** If true, then informational output is recorded in the
   *  system log (in addition to the console); if false, then it is not.
   */
  public boolean alsoLogInfo = false;

  /** Cached value of the MessageConsole object */
  //private MessageConsole console = null;
  //@ private constraint \old(console) != null ==> \not_modified(console);

  /** Cached value of the stream to use to write to the console */
  private MessageConsoleStream stream = null;
  //@ private constraint \old(stream) != null ==> \not_modified(stream);



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
  // FIXME - should get this color from the system preferences
  static final private Color errorColor = new Color(null,255,0,0);

  /**
   * Records an informational message adding a newline
   * @param msg The message to log
   */
  //@ requires msg != null;
  //@ modifies content;
  public void log(String msg) {
    getConsoleStream().println(msg);
    // Also write it to the log file, if requested.
    if (alsoLogInfo) {
      pluginLog.log(
              new Status(Status.INFO, 
                      pluginID,
                      Status.OK, msg, null));
    }
  }

  /**
   * Records an informational message without a terminating new line
   * @param msg The message to log
   */
  //@ requires msg != null;
  //@ modifies content;
  public void log_noln(String msg) {
    getConsoleStream().print(msg);
    // Also write it to the log file, if requested.
    if (alsoLogInfo) {
      pluginLog.log(
              new Status(Status.INFO, 
                      pluginID,
                      Status.OK, msg, null));
    }
  }


  /**
   * Records an error message
   * @param msg The message to log
   * @param e An associated exception (may be null)
   */
  //@ modifies content;
  public void errorlog(/*@ non_null */String msg, /*@ nullable */ Throwable e) {
    // Always put errors in the log
    pluginLog.log(
            new Status(Status.ERROR, 
                    pluginID,
                    Status.OK, msg, e));
    MessageConsoleStream cs = getConsoleStream();
    Color c = cs.getColor();
    cs.setColor(errorColor);
    cs.println(msg);
    if (e != null) e.printStackTrace(this.stream());
    cs.setColor(c);
  }

  public void flush() throws IOException {
    getConsoleStream().flush();
  }


  /**
   * Creates a PrintStream that, when written to, writes to the Eclipse Console
   * of the current log object
   * 
   * @return a PrintStream connected to the Eclipse Console
   */
  public PrintStream stream() {
    return new PrintStream(getConsoleStream());
  }
}

