package org.openjml.lsp;

import java.time.LocalTime;
import java.time.format.DateTimeFormatter;

/**
 * Centralised server-side logging: writes timestamped messages to {@code System.err}.
 */
public final class ServerLog {

    private static final DateTimeFormatter FMT =
            DateTimeFormatter.ofPattern("HH:mm:ss.SSS");

    private ServerLog() {}

    /** Write {@code msg} to {@code System.err} prefixed with the current wall-clock time and thread name. */
    public static void serverLog(String msg) {
        System.err.println("[" + LocalTime.now().format(FMT) + " " + Thread.currentThread().getName() + "] " + msg);
    }
}
