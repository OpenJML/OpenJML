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
import java.util.Arrays;
import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
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
 * The server executable path is determined by {@link #findServerPath()}.
 * Priority: (1) the {@code -D}{@link OpenJMLConstants#LSP_SERVER_PATH_PROPERTY}
 * system property (used by the test harness); (2) the user preference
 * {@link OpenJMLOptions#lspServerPathKey}; (3) bare {@code openjml-lsp},
 * which the OS resolves via {@code $PATH}.
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
     * Resolves a configured path (which may be either an OpenJML installation
     * folder or the launcher script itself) to the actual launcher script path.
     * If {@code path} is a directory, appends {@link OpenJMLConstants#LSP_LAUNCHER_SCRIPT};
     * otherwise returns it unchanged.
     */
    public static String resolveToScript(String path) {
        if (path == null || path.isBlank()) return path;
        java.io.File f = new java.io.File(path);
        if (f.isDirectory()) {
            String sep = path.endsWith("/") || path.endsWith(java.io.File.separator)
                    ? "" : java.io.File.separator;
            return path + sep + OpenJMLConstants.LSP_LAUNCHER_SCRIPT;
        }
        return path;
    }

    /**
     * Resolves the effective server path.  Priority:
     * <ol>
     *   <li>{@code -D}{@link OpenJMLConstants#LSP_SERVER_PATH_PROPERTY} system property
     *       (always takes precedence, regardless of whether the preference is set)</li>
     *   <li>User preference ({@link OpenJMLOptions#lspServerPathKey}), trimmed;
     *       blank after trimming is treated as not set</li>
     *   <li>{@link #findDefaultServerPath()} — bare {@code openjml-lsp} found via
     *       {@code $PATH}</li>
     * </ol>
     */
    public static String findServerPath() {
        // 1. System property — takes precedence over the preference field.
        String sysProp = System.getProperty(OpenJMLConstants.LSP_SERVER_PATH_PROPERTY);
        if (sysProp != null && !sysProp.isBlank()) {
            return sysProp;
        }
        // 2. User preference (set via OpenJML Preferences page), trimmed.
        String pref = OpenJMLOptions.value(OpenJMLOptions.lspServerPathKey);
        if (pref != null && !pref.trim().isBlank()) {
            return pref.trim();
        }
        return findDefaultServerPath();
    }

    /**
     * Returns the default server path when neither the system property nor the
     * user preference is set: the bare launcher script name
     * {@link OpenJMLConstants#LSP_LAUNCHER_SCRIPT}, which the OS resolves via
     * {@code $PATH}.  Used by the preferences page to describe the fallback.
     */
    public static String findDefaultServerPath() {
        return OpenJMLConstants.LSP_LAUNCHER_SCRIPT;
    }

    /**
     * Returns {@code true} if the launcher script is available at {@code path}.
     * {@code path} may be an installation folder (script name appended automatically),
     * a full script path, or a bare name with no path separator (in which case the
     * OS will resolve it via {@code $PATH} at spawn time — we return {@code true}
     * and let the process start fail if the name is not on {@code $PATH}).
     */
    public static boolean isServerAvailable(String path) {
        String script = resolveToScript(path);
        // Bare name (no separator) — trust the OS to find it on PATH.
        if (script != null
                && !script.contains("/")
                && !script.contains(java.io.File.separator)) {
            return true;
        }
        java.io.File f = new java.io.File(script);
        return f.isFile() && f.canExecute();
    }

    /**
     * Sends OpenJML analysis settings to the server as initialization options,
     * matching the fields in {@link org.openjml.lsp.OpenJMLSettings}.
     */
    @Override
    public Object getInitializationOptions(URI rootUri) {
        Map<String, Object> opts = OpenJMLOptions.buildInitializationOptions();
        // Advertise support for $/openjml/actionMessage so the server routes
        // advisory and error messages through the richer custom notification
        // instead of plain window/logMessage.
        opts.put("supportsActionMessages", true);
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
            String script = resolveToScript(path);
            if (isServerAvailable(path)) {
                setCommands(Arrays.asList(script));
                break;
            }
            Console.errorlog("OpenJML server launcher not found or not executable: " + script);

            Display display = Display.getDefault();
            if (display == null || display.isDisposed()) {
                throw new IOException("OpenJML launcher not found or not executable: " + script);
            }
            boolean[] retry = { false };
            display.syncExec(() -> {
                Shell shell = display.getActiveShell();
                String msg =
                        "The OpenJML LSP server launcher was not found or is not executable:\n\n"
                        + "  " + script + "\n\n"
                        + "Without a running server, all OpenJML features (type-checking, ESC,\n"
                        + "RAC, syntax coloring, etc.) will be non-functional.\n\n"
                        + "Open Preferences to set the OpenJML installation path, or Cancel to\n"
                        + "continue without OpenJML (the plugin will be non-functional for this session).";
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
                        "OpenJML installation not configured; server startup cancelled by user.");
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
        String script = resolveToScript(findServerPath());
        Console.errorlog("OpenJML LSP server stopped unexpectedly (launcher: " + script + ")");
        Display display = Display.getDefault();
        Shell shell = display != null ? display.getActiveShell() : null;
        String msg =
                "The OpenJML LSP server has stopped unexpectedly.\n\n"
                + "Server launcher: " + script + "\n\n"
                + "Without a running server, all OpenJML features (type-checking, ESC, RAC,\n"
                + "syntax coloring, etc.) are non-functional.\n\n"
                + "Restart the server, open Preferences to fix the OpenJML installation path,\n"
                + "or continue without OpenJML for the rest of this Eclipse session.";
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
     * Intercepts raw LSP notifications before LSP4E routing.
     *
     * <p>Handles two notification methods:
     * <ul>
     *   <li>{@code $/openjml/actionMessage} — sent by the server to capable clients.
     *       Logs to the JML Console (severity-coloured) and optionally shows an
     *       action dialog (e.g. "Open Preferences").</li>
     *   <li>{@code window/logMessage} — fallback for generic clients, and for
     *       {@code Log}-type verbose output that never needs a dialog.
     *       Routing by type: Log (4) → {@link Console#logRaw} (no timestamp);
     *       everything else → {@link Console#log} (with timestamp).</li>
     * </ul>
     */
    @Override
    public void handleMessage(org.eclipse.lsp4j.jsonrpc.messages.Message message,
                              org.eclipse.lsp4j.services.LanguageServer server,
                              java.net.URI rootUri) {
        if (!(message instanceof org.eclipse.lsp4j.jsonrpc.messages.NotificationMessage n)) return;

        if ("$/openjml/actionMessage".equals(n.getMethod())) {
            handleActionMessage(n.getParams());
            return;
        }

        if ("window/logMessage".equals(n.getMethod())) {
            Object params = n.getParams();
            String text = extractField(params, "message");
            if (text == null) return;
            boolean isLog = (params instanceof org.eclipse.lsp4j.MessageParams mp)
                    ? mp.getType() == org.eclipse.lsp4j.MessageType.Log
                    : extractIntField(params, "type", 3) == 4;
            if (isLog) Console.logRaw(text);
            else       Console.log(text);
        }
    }

    /**
     * Handles a {@code $/openjml/actionMessage} notification.
     *
     * <p>Logs the message to the JML Console with severity-appropriate coloring,
     * then — if the {@code actions} list is non-empty — shows a dialog on the SWT
     * UI thread whose buttons correspond to the action items.
     */
    private static void handleActionMessage(Object rawParams) {
        String text    = extractField(rawParams, "message");
        int    type    = extractIntField(rawParams, "type", 3);
        java.util.List<?> actions = extractListField(rawParams, "actions");

        if (text == null || text.isBlank()) return;

        // Log to the JML Console (errors and warnings in red).
        if (type == 1 || type == 2) Console.errorlog(text);
        else if (type == 4)         Console.logRaw(text);
        else                        Console.log(text);

        // Show a dialog only when there are action items.
        Console.log("[OpenJML] actionMessage: type=" + type + " actions=" + actions.size()
                + " params.class=" + (rawParams == null ? "null" : rawParams.getClass().getName()));
        if (actions == null || actions.isEmpty()) return;

        Display display = Display.getDefault();
        if (display == null || display.isDisposed()) return;
        display.asyncExec(() -> {
            Shell shell = display.getActiveShell();
            String[] labels = actions.stream()
                    .map(a -> { String t = extractField(a, "title"); return t != null ? t : "OK"; })
                    .toArray(String[]::new);
            int dialogStyle = (type == 1) ? MessageDialog.ERROR : MessageDialog.WARNING;
            MessageDialog dialog = new MessageDialog(shell, "OpenJML", null,
                    text, dialogStyle, labels, 0);
            int choice = dialog.open();
            if (choice < 0 || choice >= actions.size()) return;
            String kind   = extractField(actions.get(choice), "kind");
            String target = extractField(actions.get(choice), "target");
            if ("openPreferences".equals(kind)) {
                String pageId = resolvePreferencesPageId(target);
                var prefDialog = PreferencesUtil.createPreferenceDialogOn(shell, pageId, null, null);
                if (prefDialog != null) prefDialog.open();
            }
            // "dismiss" and unknown kinds: no-op
        });
    }

    /**
     * Maps an abstract preference target name (sent by the server) to the
     * fully-qualified Eclipse preference page ID.
     */
    private static String resolvePreferencesPageId(String target) {
        if ("toolOptions".equals(target)) return "org.jmlspecs.openjml.eclipse.ToolOptionsPage";
        return "org.jmlspecs.openjml.eclipse.SettingsPage";  // "settings" and unknown
    }

    // -----------------------------------------------------------------------
    // Generic JSON field extraction helpers
    // -----------------------------------------------------------------------
    // Params arriving in handleMessage may be either typed lsp4j POJOs (if
    // deserialized before routing) or raw Gson JsonObjects from a different
    // OSGi classloader.  We avoid direct Gson API calls and use toString()
    // parsing with regex as a universal fallback.

    /**
     * Extracts a named string field from an LSP params object.
     * Works whether params is a typed POJO (via reflection) or a raw JSON object
     * (via {@code toString()} regex).
     */
    private static String extractField(Object params, String fieldName) {
        if (params == null) return null;
        // Try reflection first (works for typed POJOs and Gson JsonObject).
        try {
            var method = params.getClass().getMethod("get"
                    + Character.toUpperCase(fieldName.charAt(0)) + fieldName.substring(1));
            Object val = method.invoke(params);
            return val instanceof String s ? s : null;
        } catch (Exception ignored) {}
        // Fallback: regex on toString() JSON representation.
        String json = params.toString();
        var m = java.util.regex.Pattern
                .compile("\"" + java.util.regex.Pattern.quote(fieldName)
                        + "\"\\s*:\\s*\"((?:[^\"\\\\]|\\\\.)*)\"")
                .matcher(json);
        if (m.find()) {
            return m.group(1)
                    .replace("\\\"", "\"")
                    .replace("\\\\", "\\")
                    .replace("\\n", "\n")
                    .replace("\\r", "\r")
                    .replace("\\t", "\t");
        }
        return null;
    }

    /** Extracts a named integer field; returns {@code defaultValue} if absent or unparseable. */
    private static int extractIntField(Object params, String fieldName, int defaultValue) {
        if (params == null) return defaultValue;
        // Try reflection.
        try {
            var method = params.getClass().getMethod("get"
                    + Character.toUpperCase(fieldName.charAt(0)) + fieldName.substring(1));
            Object val = method.invoke(params);
            if (val instanceof Number n) return n.intValue();
            if (val != null) return Integer.parseInt(val.toString());
        } catch (Exception ignored) {}
        // Fallback: regex.
        String json = params.toString();
        var m = java.util.regex.Pattern
                .compile("\"" + java.util.regex.Pattern.quote(fieldName) + "\"\\s*:\\s*(\\d+)")
                .matcher(json);
        if (m.find()) { try { return Integer.parseInt(m.group(1)); } catch (NumberFormatException ignored) {} }
        return defaultValue;
    }

    /**
     * Extracts a named array field as a {@code List<?>}.
     *
     * <p>Tries three strategies in order:
     * <ol>
     *   <li>Gson {@code JsonObject.get(fieldName)} → iterate via {@code size()} /
     *       {@code get(int)} — works for any Gson version and any OSGi classloader.</li>
     *   <li>Typed POJO {@code getFieldName()} returning a {@link java.util.List}.</li>
     *   <li>Parse the JSON {@code toString()} to count array elements (last resort).</li>
     * </ol>
     * Returns an empty list if the field is absent or cannot be read.
     */
    private static java.util.List<?> extractListField(Object params, String fieldName) {
        if (params == null) return java.util.List.of();

        // Strategy 1: Gson JsonObject.get(String) → JsonArray via size()/get(int).
        // Does NOT use asList() (added in Gson 2.10) so it works with any Gson bundle.
        try {
            java.lang.reflect.Method get = params.getClass().getMethod("get", String.class);
            Object arr = get.invoke(params, fieldName);
            if (arr != null) {
                java.lang.reflect.Method size  = arr.getClass().getMethod("size");
                java.lang.reflect.Method getAt = arr.getClass().getMethod("get", int.class);
                int n = (int) size.invoke(arr);
                var list = new java.util.ArrayList<>(n);
                for (int i = 0; i < n; i++) list.add(getAt.invoke(arr, i));
                return java.util.Collections.unmodifiableList(list);
            }
        } catch (Exception ignored) {}

        // Strategy 2: typed POJO getter (e.g. getActions())
        try {
            java.lang.reflect.Method getter = params.getClass().getMethod("get"
                    + Character.toUpperCase(fieldName.charAt(0)) + fieldName.substring(1));
            Object val = getter.invoke(params);
            if (val instanceof java.util.List<?> list) return list;
        } catch (Exception ignored) {}

        return java.util.List.of();
    }

    @Override
    public String toString() {
        return "OpenJML LSP Server " + super.toString();
    }
}
