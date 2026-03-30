/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.IOException;
import java.net.URI;
import java.net.URL;
import java.util.Arrays;
import java.util.Map;

import org.eclipse.core.runtime.Platform;
import org.eclipse.lsp4e.server.ProcessStreamConnectionProvider;

/**
 * Launches the openjml-lsp server process and connects to it via
 * stdin/stdout using the LSP4E framework.
 *
 * The server executable path is taken from the preference
 * {@link Options#lspServerPathKey} if set; otherwise it defaults to
 * an {@code openjml-lsp} script in the same directory as the Eclipse
 * installation.
 */
public class OpenJMLStreamConnectionProvider extends ProcessStreamConnectionProvider {

    static {
        System.err.println("[OpenJML] OpenJMLStreamConnectionProvider class loaded");
    }

    public OpenJMLStreamConnectionProvider() {
        String path = findServerPath();
        System.err.println("[OpenJML] OpenJMLStreamConnectionProvider created, path=" + path);
        setCommands(Arrays.asList(path));
        setWorkingDirectory(System.getProperty("user.dir"));
    }

    /**
     * Resolves the path to the openjml-lsp launcher script.
     * Priority:
     *   1. User preference (Options.lspServerPathKey)
     *   2. Directory of the Eclipse install (Platform.getInstallLocation)
     */
    public static String findServerPath() {
        // 1. User preference (set via OpenJML Preferences page)
        String pref = OpenJMLOptions.value(OpenJMLOptions.lspServerPathKey);
        if (pref != null && !pref.isBlank()) {
            return pref;
        }
        // 2. System property — used by the test harness to inject the dev path
        //    without modifying workspace preferences.
        String sysProp = System.getProperty("openjml.lsp.server.path");
        if (sysProp != null && !sysProp.isBlank()) {
            return sysProp;
        }
        // 3. Script alongside the Eclipse install (release layout)
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

    /**
     * Sends OpenJML analysis settings to the server as initialization options,
     * matching the fields in {@link org.openjml.lsp.OpenJMLSettings}.
     */
    @Override
    public void start() throws IOException {
        System.err.println("[OpenJML] OpenJMLStreamConnectionProvider.start() called");
        String path = findServerPath();
        java.io.File f = new java.io.File(path);
        if (!f.isFile() || !f.canExecute()) {
            Console.errorlog("[OpenJML] server script not found or not executable: " + path);
            showServerNotFoundDialog(path);
            throw new IOException("openjml-lsp not found or not executable: " + path);
        }
        // Write the generated preferences file before starting the server so
        // it is available when getInitializationOptions() is called.
        OpenJMLOptions.writePropertiesFile();
        super.start();
        System.err.println("[OpenJML] OpenJMLStreamConnectionProvider.start() completed");
    }

    @Override
    public Object getInitializationOptions(URI rootUri) {
        Map<String, Object> opts = OpenJMLOptions.buildInitializationOptions();
        Console.log("[OpenJML] Sending initializationOptions: checkTriggerOn="
                + opts.get("checkTriggerOn") + ", escEngine=" + opts.get("escEngine"));
        return opts;
    }

    /**
     * Returns true if the server script is present and executable at the
     * currently configured path.
     */
    public static boolean isServerAvailable() {
        java.io.File f = new java.io.File(findServerPath());
        return f.isFile() && f.canExecute();
    }

    /**
     * Shows a warning dialog offering to open OpenJML Preferences so the
     * user can set the LSP server path.  Safe to call from any thread.
     */
    public static void showServerNotFoundDialog(String path) {
        org.eclipse.swt.widgets.Display display =
                org.eclipse.swt.widgets.Display.getDefault();
        if (display == null) return;
        display.asyncExec(() -> {
            org.eclipse.swt.widgets.Shell shell = display.getActiveShell();
            String message =
                    "The OpenJML LSP server script was not found at:\n\n  " + path + "\n\n"
                    + "OpenJML features (error markers, ESC, syntax coloring, etc.) "
                    + "will not work until the path is configured.\n\n"
                    + "Click \"Open Preferences\" to set the LSP Server Path now.";
            org.eclipse.jface.dialogs.MessageDialog dialog =
                    new org.eclipse.jface.dialogs.MessageDialog(
                            shell,
                            "OpenJML: Server Not Configured",
                            null,
                            message,
                            org.eclipse.jface.dialogs.MessageDialog.WARNING,
                            new String[]{"Open Preferences", "Dismiss"},
                            0);
            if (dialog.open() == 0) {   // "Open Preferences"
                org.eclipse.ui.dialogs.PreferencesUtil
                        .createPreferenceDialogOn(shell,
                                "org.jmlspecs.openjml.eclipse.SettingsPage",
                                null, null)
                        .open();
            }
        });
    }

    /**
     * Intercept every incoming server message.  {@code window/logMessage}
     * notifications are routed to the JML Console so proof results and other
     * server messages are visible to the user without opening the Error Log.
     */
    @Override
    public void handleMessage(org.eclipse.lsp4j.jsonrpc.messages.Message message,
                              org.eclipse.lsp4j.services.LanguageServer server,
                              java.net.URI rootUri) {
        if (message instanceof org.eclipse.lsp4j.jsonrpc.messages.NotificationMessage n
                && "window/logMessage".equals(n.getMethod())) {
            Object params = n.getParams();
            String text = extractLogMessageText(params);
            if (text != null) Console.log("[OpenJML] " + text);
        }
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
