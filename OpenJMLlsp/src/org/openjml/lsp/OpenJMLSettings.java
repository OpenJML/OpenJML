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
     * Check mode: {@code "check"} (default, JML type-checking only) or
     * {@code "esc"} (extended static checking via SMT solver — slower).
     */
    public volatile String mode = "check";

    /** Returns the OpenJML command-line flag for the configured mode. */
    public String modeFlag() {
        return "esc".equalsIgnoreCase(mode) ? "--esc" : "--check";
    }
}
