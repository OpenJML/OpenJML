package org.openjml.lsp;

/**
 * User-configurable settings for the OpenJML language server.
 *
 * Settings arrive via two channels:
 * <ul>
 *   <li>{@code initializationOptions} in the {@code initialize} request — the
 *       object is deserialized directly as an {@code OpenJMLSettings}.</li>
 *   <li>{@code workspace/didChangeConfiguration} — the settings object is
 *       expected to have an {@code "openjml"} key whose value is an
 *       {@code OpenJMLSettings}-shaped JSON object.</li>
 * </ul>
 *
 * All fields are {@code volatile} so that reads on the async check-executor
 * thread always see values written on the LSP dispatch thread.
 */
public class OpenJMLSettings {

    /**
     * Path to the OpenJML specs directory, passed as {@code --specs-path}.
     * {@code null} or empty means use the server's default (the
     * {@code OPENJML_SPECS} environment variable set by the launcher script).
     */
    public volatile String specsPath;

    /**
     * Path to the SMT solvers directory, passed as {@code --solvers-path}.
     * {@code null} or empty means use the server's default (the
     * {@code OPENJML_SOLVERS} environment variable set by the launcher script).
     */
    public volatile String solversPath;

    /**
     * Source root(s) for resolving cross-file references, passed as
     * {@code -sourcepath}.  Multiple roots may be separated by the OS path
     * separator ({@code :} on Unix, {@code ;} on Windows).
     * {@code null} or empty means no {@code -sourcepath} is passed.
     */
    public volatile String sourcePath;

    /**
     * Classpath for resolving pre-compiled dependencies, passed as
     * {@code -classpath}.  Multiple entries may be separated by the OS path
     * separator ({@code :} on Unix, {@code ;} on Windows).
     * {@code null} or empty means no {@code -classpath} is passed.
     */
    public volatile String classPath;

    /**
     * Check mode: {@code "check"} (default, JML type-checking only) or
     * {@code "esc"} (extended static checking via SMT solver — slower).
     */
    public volatile String mode = "check";

    /**
     * When to run the check:
     * <ul>
     *   <li>{@code "edit"} (default) — check on every document change; the
     *       current editor buffer (possibly unsaved) is written to a temp file
     *       and passed to OpenJML.</li>
     *   <li>{@code "save"} — check only when the file is saved; the file on
     *       disk is passed directly to OpenJML, avoiding temp-file overhead.
     *       Diagnostics update when you save, not as you type.</li>
     * </ul>
     * In both modes the file is also checked when it is first opened.
     */
    public volatile String triggerOn = "edit";

    /** Returns the OpenJML command-line flag for the configured mode. */
    public String modeFlag() {
        return "esc".equalsIgnoreCase(mode) ? "--esc" : "--check";
    }

    /** Returns {@code true} if checks should fire on every edit. */
    public boolean isEditTriggered() {
        return !"save".equalsIgnoreCase(triggerOn);
    }
}
