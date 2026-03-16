/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

/**
 * Simple console for OpenJML LSP-related messages in Eclipse.
 *
 * <p>Opens (or reuses) a {@code MessageConsole} named "OpenJML LSP" and
 * provides a single static {@link #log(String)} method so that command
 * handlers and the stream connection provider can write status lines
 * without depending on the legacy {@link Log} / {@link ConsoleLogger}
 * infrastructure.
 *
 * <p>Usage:
 * <pre>
 *     LspConsole.log("OpenJML: starting ESC on " + file);
 * </pre>
 */
public class LspConsole {

    private static final String CONSOLE_NAME = "OpenJML LSP";

    private static MessageConsole console;

    /** Returns (or lazily creates) the shared OpenJML LSP console. */
    public static synchronized MessageConsole getConsole() {
        if (console != null) return console;
        IConsoleManager mgr = ConsolePlugin.getDefault().getConsoleManager();
        for (IConsole c : mgr.getConsoles()) {
            if (CONSOLE_NAME.equals(c.getName()) && c instanceof MessageConsole) {
                console = (MessageConsole) c;
                return console;
            }
        }
        console = new MessageConsole(CONSOLE_NAME, null);
        console.setWaterMarks(10 * 1024, 10 * 1024 * 1024);
        mgr.addConsoles(new IConsole[] { console });
        return console;
    }

    /**
     * Append {@code message} followed by a newline to the OpenJML LSP console.
     * Safe to call from any thread.
     */
    public static void log(String message) {
        try (MessageConsoleStream stream = getConsole().newMessageStream()) {
            stream.println(message);
        } catch (Exception ignored) {}
    }
}
