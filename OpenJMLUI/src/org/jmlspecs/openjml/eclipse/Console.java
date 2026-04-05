/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleFactory;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

/**
 * Simple console for OpenJML LSP-related messages in Eclipse.
 *
 * <p>Opens (or reuses) a {@code MessageConsole} named "JML Console" and
 * provides a static {@link #log(String)} and {@link #errorlog(String)} methods
 * so that command handlers and the stream connection provider can write status lines.
 *
 * <p>Usage:
 * <pre>
 *     Console.log("OpenJML: starting ESC on " + file);
 * </pre>
 */
public class Console {

    /** The user-visible name that labels the JML Console */
    private static final String CONSOLE_NAME = Messages.OpenJMLUI_ConsoleTitle;
    
    /** The factory for creating consoles. The name of this class is used in plugin.xml */
    public static class ConsoleFactory implements IConsoleFactory {

        /** The Factory method invoked by Eclipse when asked to create a new console */
        @Override
        public void openConsole() {
            getJMLConsole();
            Console.show();
        }

        /** Returns the JML Console, creating it if necessary; 'show's it if the argument is true. */
        public static /* @ non_null */ MessageConsole getJMLConsole() {
            MessageConsole console = null;
            IConsoleManager consoleManager = ConsolePlugin.getDefault().getConsoleManager();
            
            // Check whether our singleton JML console already exists
            IConsole[] existing = consoleManager.getConsoles();
            for (int i = 0; i < existing.length; ++i) {
                if (existing[i].getName().equals(CONSOLE_NAME)) {
                    console = (MessageConsole) existing[i];
                    break;
                }
            }
            
            // If the JML console does not yet exist, create it
            if (console == null) {
                console = new MessageConsole(CONSOLE_NAME, null);
                consoleManager.addConsoles(new IConsole[] { console });
            }
            
            // cap it at 10M characters
            console.setWaterMarks(10000, 10000000);
            return console;
        }
    }

    /** Cached instance of the singleton OpenJML Console */
    private static MessageConsole console;

    /** Returns (lazily creating) the shared OpenJML console. */
    public static synchronized MessageConsole getConsole() {
        if (console == null) console = ConsoleFactory.getJMLConsole();
        return console;
    }

    /**
     * Shared stream for Info-level output.  Reusing one stream avoids Eclipse's
     * IOConsolePartitioner partition-boundary behaviour, which can drop the
     * trailing newline of a closed stream when a new stream opens immediately
     * after — causing successive messages to run together on one line.
     */
    private static MessageConsoleStream normalStream;

    private static synchronized MessageConsoleStream getNormalStream() {
        if (normalStream == null || normalStream.isClosed()) {
            normalStream = getConsole().newMessageStream();
        }
        return normalStream;
    }

    /** Returns a timestamp prefix of the form {@code [HH:mm:ss] } (24-hour clock). */
    private static String ts() {
        return "[" + java.time.LocalTime.now()
                .format(java.time.format.DateTimeFormatter.ofPattern("HH:mm:ss")) + "] ";
    }

    /**
     * Append {@code message} followed by a newline to the OpenJML console,
     * without adding a timestamp.  Use this for messages that already carry
     * their own timestamp (e.g. forwarded server log lines).
     * Safe to call from any thread.
     */
    public static synchronized void logRaw(String message) {
        try {
            getNormalStream().println(message);
        } catch (Exception ignored) {}
    }

    /**
     * Append a timestamped {@code message} followed by a newline to the OpenJML console.
     * If the message contains embedded newlines, continuation lines are indented to align
     * under the first character after the timestamp.
     * Safe to call from any thread.
     */
    public static synchronized void log(String message) {
        try {
            String prefix = ts();
            String indent = " ".repeat(prefix.length());
            String msg = message.endsWith("\n") ? message.substring(0, message.length() - 1) : message;
            getNormalStream().println(prefix + msg.replace("\n", "\n" + indent));
        } catch (Exception ignored) {}
    }

    /**
     * Append {@code message} followed by a newline to the OpenJML console in red font,
     * without adding a timestamp.  Use this for messages that already carry their own
     * timestamp (e.g. forwarded server error lines).
     * Safe to call from any thread.
     */
    public static void errorlogRaw(String message) {
        try (MessageConsoleStream stream = getConsole().newMessageStream()) {
            stream.setColor(new org.eclipse.swt.graphics.Color(255, 0, 0));
            stream.println(message);
        } catch (Exception ignored) {}
    }

    /**
     * Append a timestamped {@code message} followed by a newline to the OpenJML console,
     * in red font. Safe to call from any thread.
     */
    public static void errorlog(String message) {
        errorlog(message, null);
    }

    /**
     * Append a timestamped {@code message} followed by a newline to the OpenJML console
     * in red font; if {@code ex} is non-null, appends the full stack trace on subsequent
     * lines. Safe to call from any thread.
     */
    public static void errorlog(String message, Throwable ex) {
        try (MessageConsoleStream stream = getConsole().newMessageStream()) {
            stream.setColor(new org.eclipse.swt.graphics.Color(255,0,0)); // Red for errors
            String prefix = ts();
            String indent = " ".repeat(prefix.length());
            String msg = message.endsWith("\n") ? message.substring(0, message.length() - 1) : message;
            stream.println(prefix + msg.replace("\n", "\n" + indent));
            if (ex != null) {
                java.io.StringWriter sw = new java.io.StringWriter();
                ex.printStackTrace(new java.io.PrintWriter(sw));
                stream.print(sw.toString());
            }
            show();
        } catch (Exception ignored) {}
    }
    
    /** Make the console visible in the GUI */
    public static void show() {
        IConsoleManager consoleManager = ConsolePlugin.getDefault().getConsoleManager();
        consoleManager.showConsoleView(getConsole());
    }
}
