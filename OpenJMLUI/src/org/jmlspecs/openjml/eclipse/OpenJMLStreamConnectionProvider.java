/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.FilterInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URL;
import java.util.Arrays;
import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4e.server.ProcessStreamConnectionProvider;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.dialogs.PreferencesUtil;

/**
 * Launches the openjml-lsp server process and connects to it via
 * stdin/stdout using the LSP4E framework.
 *
 * The server executable path is taken from the preference
 * {@link OpenJMLOptions#lspServerPathKey} if set; otherwise it defaults to
 * an {@code openjml-lsp} script in the same directory as the Eclipse
 * installation.
 *
 * <p>If the server script is not found at startup, a dialog loops until the
 * user either configures a valid path via Preferences or cancels (in which case
 * the server is not started and all OpenJML features remain non-functional for
 * the session).
 *
 * <p>If the server process stops unexpectedly (crash or external kill), a
 * recovery dialog offers to restart it.
 */
public class OpenJMLStreamConnectionProvider extends ProcessStreamConnectionProvider {

    /** The most recently created provider instance; used for deliberate stop/restart. */
    private static volatile OpenJMLStreamConnectionProvider currentInstance;

    /**
     * {@code true} when the server was stopped intentionally (e.g. preference change,
     * Eclipse shutdown, explicit {@link #stopCurrent()}).  Prevents the EOF monitor
     * from showing a crash-recovery dialog on deliberate stops.
     */
    private volatile boolean intentionalStop = false;

    public OpenJMLStreamConnectionProvider() {
        String path = findServerPath();
        setCommands(Arrays.asList(path));
        setWorkingDirectory(System.getProperty("user.dir"));
        currentInstance = this;
    }

    /**
     * Resolves the path to the openjml-lsp launcher script.
     * Priority:
     *   1. User preference ({@link OpenJMLOptions#lspServerPathKey})
     *   2. System property — used by the test harness
     *   3. Directory of the Eclipse install ({@link Platform#getInstallLocation})
     */
    public static String findServerPath() {
        // 1. User preference (set via OpenJML Preferences page)
        String pref = OpenJMLOptions.value(OpenJMLOptions.lspServerPathKey);
        if (pref != null && !pref.isBlank()) {
            return pref;
        }
        return findDefaultServerPath();
    }

    /**
     * Resolves the server path ignoring the stored preference — checks only
     * the system property and the Eclipse install directory.  Used by the
     * preferences page to validate what path will be used when the field is
     * left blank.
     */
    public static String findDefaultServerPath() {
        // 1. System property — used by the test harness to inject the dev path
        //    without modifying workspace preferences.
        String sysProp = System.getProperty(OpenJMLConstants.LSP_SERVER_PATH_PROPERTY);
        if (sysProp != null && !sysProp.isBlank()) {
            return sysProp;
        }
        // 2. Script alongside the Eclipse install (release layout)
        try {
            URL installUrl = Platform.getInstallLocation().getURL();
            String installDir = installUrl.getPath();
            if (!installDir.endsWith("/")) installDir += "/";
            return installDir + "openjml-lsp";
        } catch (Exception e) {
            // Fall back to expecting it on PATH
            return "openjml-lsp";
        }
    }

    /** Returns {@code true} if the server script at {@code path} is present and executable. */
    public static boolean isServerAvailable(String path) {
        java.io.File f = new java.io.File(path);
        return f.isFile() && f.canExecute();
    }

    /**
     * Sends OpenJML analysis settings to the server as initialization options,
     * matching the fields in {@link org.openjml.lsp.OpenJMLSettings}.
     */
    @Override
    public Object getInitializationOptions(URI rootUri) {
        Map<String, Object> opts = OpenJMLOptions.buildInitializationOptions();
        Console.log("Sending initializationOptions: checkTriggerOn="
                + opts.get("checkTriggerOn") + ", escEngine=" + opts.get("escEngine"));
        return opts;
    }

    /**
     * Starts the server process.  If the server script is not found at the
     * currently configured path, a dialog loops until the user either sets a
     * valid path via Preferences or cancels.  Cancelling throws
     * {@link IOException}, which tells LSP4E to abandon the connection for
     * this Eclipse session.
     */
    @Override
    public void start() throws IOException {
        intentionalStop = false;

        // Loop until we have a valid server path or the user cancels.
        while (true) {
            String path = findServerPath();
            if (isServerAvailable(path)) {
                setCommands(Arrays.asList(path));
                break;
            }
            Console.errorlog("OpenJML server script not found or not executable: " + path);

            Display display = Display.getDefault();
            if (display == null || display.isDisposed()) {
                throw new IOException("openjml-lsp not found or not executable: " + path);
            }
            boolean[] retry = { false };
            display.syncExec(() -> {
                Shell shell = display.getActiveShell();
                String msg =
                        "The OpenJML LSP server script was not found or is not executable:\n\n"
                        + "  " + path + "\n\n"
                        + "Without a running server, all OpenJML features (type-checking, ESC,\n"
                        + "RAC, syntax coloring, etc.) will be non-functional.\n\n"
                        + "Open Preferences to set the server script path, or Cancel to continue\n"
                        + "without OpenJML (the plugin will be non-functional for this session).";
                MessageDialog dialog = new MessageDialog(shell,
                        "OpenJML: Server Not Found", null, msg,
                        MessageDialog.WARNING,
                        new String[] { "Open Preferences", "Cancel" }, 0);
                if (dialog.open() == 0) {
                    PreferencesUtil.createPreferenceDialogOn(shell,
                            "org.jmlspecs.openjml.eclipse.SettingsPage",
                            null, null).open();
                    retry[0] = true;
                }
            });

            if (!retry[0]) {
                throw new IOException(
                        "openjml-lsp not configured; server startup cancelled by user.");
            }
            // Path may have changed in preferences; loop to re-check.
        }

        // Write the generated preferences file before starting the server so
        // it is available when getInitializationOptions() is called.
        OpenJMLOptions.writePropertiesFile();
        Console.log("OpenJML LSP server starting: " + getCommands().get(0));
        super.start();
    }

    /**
     * Wraps the server's stdout stream to detect unexpected process death.
     * When EOF is received and the stop was not intentional, schedules a
     * crash-recovery dialog on the UI thread.
     */
    @Override
    public InputStream getInputStream() {
        InputStream real = super.getInputStream();
        if (real == null) return null;
        return new FilterInputStream(real) {
            private boolean eofReported = false;

            @Override
            public int read() throws IOException {
                int b = super.read();
                if (b == -1) onEof();
                return b;
            }

            @Override
            public int read(byte[] buf, int off, int len) throws IOException {
                int n = super.read(buf, off, len);
                if (n == -1) onEof();
                return n;
            }

            private void onEof() {
                if (!intentionalStop && !eofReported) {
                    eofReported = true;
                    Display display = Display.getDefault();
                    if (display != null && !display.isDisposed()) {
                        display.asyncExec(
                                OpenJMLStreamConnectionProvider.this::showCrashRecoveryDialog);
                    }
                }
            }
        };
    }

    /**
     * Marks the stop as intentional before delegating to the superclass,
     * so the EOF monitor does not show a crash-recovery dialog.
     */
    @Override
    public void stop() {
        intentionalStop = true;
        super.stop();
    }

    // -----------------------------------------------------------------------
    // Static lifecycle helpers (called from preferences and command handlers)
    // -----------------------------------------------------------------------

    /**
     * Stops the current server instance if one is running.  Sets
     * {@code intentionalStop} so no crash dialog appears.
     */
    public static void stopCurrent() {
        OpenJMLStreamConnectionProvider inst = currentInstance;
        if (inst != null) {
            inst.intentionalStop = true;
            inst.stop();
        }
    }

    /**
     * Asks LSP4E to (re)connect to the OpenJML language server by finding the
     * first open JML-natured project and requesting its language servers.
     * LSP4E will start the server (calling {@link #start()}) if it is not
     * already running.  Must be called on the UI thread.
     */
    public static void triggerReconnect() {
        try {
            for (IProject project : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
                if (project.isOpen() && JmlNature.hasNature(project)) {
                    LanguageServers.forProject(project)
                            .computeFirst(ls -> ls.getWorkspaceService()
                                .executeCommand(new ExecuteCommandParams(
                                        OpenJMLConstants.CMD_CLEAR_MARKERS,
                                        java.util.List.of()))
                                .exceptionally(e -> null));
                    Console.log("OpenJML LSP server reconnect requested.");
                    return;
                }
            }
            Console.log("No JML-natured project found; open a Java file "
                    + "in a JML-natured project to reconnect the OpenJML server.");
        } catch (Exception e) {
            Console.log("Server reconnect failed: " + e.getMessage());
        }
    }

    // -----------------------------------------------------------------------
    // Crash recovery
    // -----------------------------------------------------------------------

    /**
     * Shows a warning dialog telling the user the server has stopped, and
     * offers to restart it.  Called on the UI thread via {@code asyncExec}.
     */
    private void showCrashRecoveryDialog() {
        String path = findServerPath();
        Console.errorlog("OpenJML LSP server stopped unexpectedly (path: " + path + ")");
        Display display = Display.getDefault();
        Shell shell = display != null ? display.getActiveShell() : null;
        String msg =
                "The OpenJML LSP server has stopped unexpectedly.\n\n"
                + "Server path: " + path + "\n\n"
                + "Without a running server, all OpenJML features (type-checking, ESC, RAC,\n"
                + "syntax coloring, etc.) are non-functional.\n\n"
                + "Restart the server, open Preferences to fix the server path, or continue\n"
                + "without OpenJML for the rest of this Eclipse session.";
        MessageDialog dialog = new MessageDialog(shell,
                "OpenJML: Server Stopped Unexpectedly", null, msg,
                MessageDialog.WARNING,
                new String[] { "Restart", "Open Preferences", "Continue without OpenJML" }, 0);
        int choice = dialog.open();
        if (choice == 0) {
            triggerReconnect();
        } else if (choice == 1) {
            PreferencesUtil.createPreferenceDialogOn(shell,
                    "org.jmlspecs.openjml.eclipse.SettingsPage",
                    null, null).open();
            triggerReconnect();
        }
    }

    // -----------------------------------------------------------------------
    // LSP4E message interception
    // -----------------------------------------------------------------------

    /**
     * Intercept every incoming server message and route {@code window/logMessage}
     * notifications to the JML Console.
     *
     * <p>In practice {@link OpenJMLLanguageClient#logMessage} is never invoked —
     * all {@code window/logMessage} notifications arrive here and nowhere else.
     * Routing by type:
     * <ul>
     *   <li>{@code Error} (1) → {@link Console#errorlog} (red, with timestamp)</li>
     *   <li>{@code Warning} (2), {@code Info} (3) → {@link Console#log} (with timestamp)</li>
     *   <li>{@code Log} (4) → {@link Console#logRaw} (no timestamp; verbose invocation lines)</li>
     * </ul>
     */
    @Override
    public void handleMessage(org.eclipse.lsp4j.jsonrpc.messages.Message message,
                              org.eclipse.lsp4j.services.LanguageServer server,
                              java.net.URI rootUri) {
        if (!(message instanceof org.eclipse.lsp4j.jsonrpc.messages.NotificationMessage n)
                || !"window/logMessage".equals(n.getMethod())) return;
        Object params = n.getParams();
        String text = extractLogMessageText(params);
        if (text == null) return;
        int type = extractMessageType(params);
        if (type == 1) {
            Console.errorlog(text);
        } else if (type == 4) {
            Console.logRaw(text);
        } else {
            Console.log(text);
        }
    }

    /** Returns the numeric {@code type} field from {@code window/logMessage} params, or 3 (Info) if unknown. */
    private static int extractMessageType(Object params) {
        if (params instanceof org.eclipse.lsp4j.MessageParams mp) {
            var t = mp.getType();
            return t == null ? 3 : t.getValue();
        }
        String json = params == null ? "" : params.toString();
        var m = java.util.regex.Pattern.compile("\"type\"\\s*:\\s*(\\d+)").matcher(json);
        if (m.find()) { try { return Integer.parseInt(m.group(1)); } catch (NumberFormatException ignored) {} }
        return 3;
    }

    /**
     * Extracts the "message" field from a {@code window/logMessage} params object.
     *
     * The params may be a typed {@link org.eclipse.lsp4j.MessageParams} (if LSP4J has
     * already deserialized it) or a raw Gson {@code JsonObject} (if accessed before
     * LSP4J routing). We avoid a direct Gson class reference to sidestep OSGi
     * classloader issues and instead fall back to {@code toString()} parsing.
     */
    private static String extractLogMessageText(Object params) {
        if (params == null) return null;
        if (params instanceof org.eclipse.lsp4j.MessageParams mp) {
            return mp.getMessage();
        }
        // params is likely a Gson JsonObject from a different classloader.
        // JsonObject.toString() produces JSON like {"type":3,"message":"..."}.
        // Use a simple regex to extract the message field.
        String json = params.toString();
        var m = java.util.regex.Pattern
                .compile("\"message\"\\s*:\\s*\"((?:[^\"\\\\]|\\\\.)*)\"")
                .matcher(json);
        if (m.find()) {
            // Unescape basic JSON escape sequences
            return m.group(1)
                    .replace("\\\"", "\"")
                    .replace("\\\\", "\\")
                    .replace("\\n", "\n")
                    .replace("\\r", "\r")
                    .replace("\\t", "\t");
        }
        return null;
    }

    @Override
    public String toString() {
        return "OpenJML LSP Server " + super.toString();
    }
}
