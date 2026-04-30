package org.openjml.lsp;

import java.util.List;

/**
 * Settings received from the LSP client — the direct Gson deserialization
 * target for both {@code initializationOptions} and
 * {@code workspace/didChangeConfiguration} payloads.
 *
 * <p>Every field maps one-to-one to a JSON key sent by the client.
 * <strong>No field is computed or assembled by the server.</strong>
 * Client-specific fields that are absent in a given client's payload
 * will be {@code null} (or the Java primitive default), which
 * {@link OpenJMLWorkspaceService#applyUpdate} treats as "not provided —
 * leave the current runtime value unchanged."
 *
 * <p>After deserialization, {@link OpenJMLWorkspaceService#applyUpdate}
 * merges these values into the live {@link OpenJMLSettings} runtime object,
 * assembling effective paths where needed (e.g., VS Code generic-client
 * mode: {@code sourcePath = userSourcePath + workspaceFolderPaths}).
 */
public class ClientSettings {

    // -----------------------------------------------------------------------
    // Eclipse-specific: per-project configurations
    // -----------------------------------------------------------------------

    /**
     * Per-project configurations sent by the Eclipse plugin.  Each entry
     * corresponds to one open Eclipse project with the JML nature.
     * {@code null} for all other clients (VS Code, bare LSP).
     */
    public List<ProjectConfig> projects;

    // -----------------------------------------------------------------------
    // Global / single-project path settings
    // -----------------------------------------------------------------------

    /**
     * Project-independent OpenJML command-line options prepended verbatim
     * to every tool invocation.
     */
    public List<String> toolOptions;

    /**
     * Path to the OpenJML specs directory ({@code --specs-path}).
     * Empty or null means use the server default.
     * For VS Code: the user's {@code openjml.specsPath} setting.
     * For Eclipse: the assembled specs path (already fully qualified).
     */
    public String specsPath;

    /**
     * Source root(s) for resolving cross-file references ({@code -sourcepath}).
     * For VS Code: the user's {@code openjml.sourcePath} setting (often empty);
     *   the server assembles the effective path by appending
     *   {@link #workspaceFolderPaths}.
     * For Eclipse: the fully assembled source path (sent pre-assembled).
     */
    public String sourcePath;

    /**
     * Classpath for pre-compiled dependencies ({@code -classpath}).
     * For VS Code: the user's {@code openjml.classPath} setting (often empty);
     *   the server assembles the effective path from this plus
     *   {@code javaOutputDir} and {@code racOutputDir}.
     * For Eclipse: the fully assembled class path (sent pre-assembled).
     */
    public String classPath;

    /**
     * The IDE's Java compiler output directory.  Used in VS Code generic
     * mode to build the classpath and as the default RAC {@code -d}.
     */
    public String javaOutputDir;

    /**
     * RAC output directory ({@code -d}).  Relative paths are resolved
     * against the workspace root.
     */
    public String racOutputDir;

    /**
     * Mode selector: {@code true} (default) — generic/VS Code client; the server
     * assembles effective paths from {@link #workspaceFolderPaths}, {@link #sourcePath},
     * {@link #classPath}, etc.  {@code false} — non-generic client (e.g. Eclipse/JDT);
     * paths are already fully assembled in {@link #sourcePath}, {@link #classPath}, etc.
     *
     * <p>Generic clients may omit this field; the default {@code true} is the right
     * behavior for any client that is not pre-assembling paths itself.
     */
    public Boolean genericMode;

    /**
     * VS Code / generic-client: joined workspace folder paths
     * (OS path-separator-delimited).  Used only when {@link #genericMode} is {@code true}.
     */
    public String workspaceFolderPaths;

    // -----------------------------------------------------------------------
    // Behavior settings
    // -----------------------------------------------------------------------

    /** When to run {@code --check}: {@code "edit"}, {@code "save"}, or {@code "manual"}. */
    public String checkTriggerOn;

    /** When to run {@code --esc}: {@code "manual"} or {@code "save"}. */
    public String escTriggerOn;

    /**
     * Syntax coloring scope: {@code "preserve Java coloring"} or
     * {@code "overwrite Java coloring"}.
     */
    public String syntaxColoringScope;

    /**
     * Syntax coloring strategy: {@code "ast"} or {@code "regex"}.
     */
    public String syntaxColoringStrategy;

    /**
     * ESC engine: {@code "fresh"} (subprocess) or {@code "concurrent"}
     * (in-process).
     */
    public String escEngine;

    /**
     * Maximum concurrent ESC tasks.  {@code null} = not provided (leave current value unchanged).
     */
    public Integer escThreads;

    /**
     * Whether the outline returns integrated Java+JML symbols ({@code true})
     * or JML-only symbols ({@code false}).  {@code null} = not provided.
     */
    public Boolean useIntegratedOutline;

    /**
     * Whether the server should use incremental text-document sync.
     * {@code null} = not provided (server keeps its default of {@code true}).
     */
    public Boolean incrementalSync;

    /**
     * {@code true} if the client understands the
     * {@code $/openjml/actionMessage} custom notification.
     * {@code null} = not provided.
     */
    public Boolean supportsActionMessages;

    /**
     * Java-vs-JML-only master switch: {@code "full"} or {@code "jml-only"}.
     * {@code null} = unset; server applies client-based default.
     */
    public String javaMode;

    /**
     * Known-client hint: {@code "generic"}, {@code "vscode-java"},
     * {@code "eclipse-jdt"}, {@code "intellij"}, etc.
     */
    public String client;

    /**
     * Returns a {@code ClientSettings} instance populated with the server's
     * built-in defaults.  Used to initialize {@link OpenJMLSettings#clientSettings}
     * before the first client configuration message arrives, so that all
     * helper methods can read from {@code clientSettings} without null-checking.
     */
    /** Default number of threads in the ESC thread pool. */
    public static final int DEFAULT_ESC_THREADS = 5;

    public static ClientSettings createDefaults() {
        ClientSettings d = new ClientSettings();
        d.checkTriggerOn         = "edit";
        d.escTriggerOn           = "manual";
        d.syntaxColoringScope    = "preserve Java coloring";
        d.syntaxColoringStrategy = "ast";
        d.escEngine              = "fresh";
        d.escThreads             = DEFAULT_ESC_THREADS;
        d.genericMode            = true;
        d.useIntegratedOutline   = true;
        d.incrementalSync        = true;
        d.supportsActionMessages = false;
        d.client                 = "generic";
        return d;
    }
}
