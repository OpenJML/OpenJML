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
     * Path to an OpenJML {@code .properties} file, passed as {@code --properties}.
     * Options in this file are read before command-line args, so IDE settings
     * (specsPath, solversPath, etc.) and invocation-specific flags ({@code --esc},
     * {@code --method}) override it.
     *
     * <p>If {@code null} or empty the server auto-discovers {@code openjml.properties}
     * in the workspace root (set during the LSP {@code initialize} handshake).
     */
    public volatile String propertiesFile;

    /**
     * Path to the OpenJML specs directory, passed as {@code --specs-path}.
     * {@code null} or empty means use the server's default.
     */
    public volatile String specsPath;

    /**
     * Path to the SMT solvers directory, passed as {@code --solvers-path}.
     * {@code null} or empty means use the server's default.
     */
    public volatile String solversPath;

    /**
     * Source root(s) for resolving cross-file references, passed as
     * {@code -sourcepath}.  Colon-separated on Unix, semicolon on Windows.
     */
    public volatile String sourcePath;

    /**
     * Workspace folder paths supplied by the editor at {@code initialize} time,
     * path-separator-separated.  Not part of the client JSON settings — set
     * programmatically by {@code OpenJMLLanguageServer.initialize()}.
     * These are appended to the effective {@code -sourcepath} after any temp
     * directory but before the user-supplied {@link #sourcePath}.
     */
    public volatile String workspaceFolderPaths;

    /**
     * Classpath for pre-compiled dependencies, passed as {@code -classpath}.
     * Colon-separated on Unix, semicolon on Windows.
     */
    public volatile String classPath;

    /**
     * When {@code true} (default), the outline ({@code textDocument/documentSymbol})
     * returns all Java and JML symbols together — an integrated view.
     * When {@code false}, only JML-specific symbols (ghost, model) are returned,
     * complementing a competing Java outline provider (e.g. Red Hat Java extension in VS Code).
     * Users can collapse unwanted sections in either mode.
     */
    public volatile Boolean useIntegratedOutline = true;

    /**
     * When to run the {@code --check} pass:
     * <ul>
     *   <li>{@code "edit"} (default) — check on every document change (debounced)</li>
     *   <li>{@code "save"} — check only when the file is saved</li>
     * </ul>
     * In both modes a check always runs when the file is first opened or saved.
     */
    public volatile String checkTriggerOn = "edit";

    /**
     * When to run the {@code --esc} pass:
     * <ul>
     *   <li>{@code "manual"} (default) — only on explicit command ({@code openjml.runEsc})</li>
     *   <li>{@code "save"} — on every save</li>
     *   <li>{@code "edit"} — on every document change (debounced; expensive)</li>
     * </ul>
     */
    public volatile String escTriggerOn = "manual";

    /** Returns {@code true} if --check should fire on every edit. */
    public boolean isCheckOnEdit() { return !"save".equalsIgnoreCase(checkTriggerOn); }

    /** Returns {@code true} if --esc should fire on every edit. */
    public boolean isEscOnEdit()   { return "edit".equalsIgnoreCase(escTriggerOn); }

    /** Returns {@code true} if --esc should fire on save. */
    public boolean isEscOnSave()   { return "save".equalsIgnoreCase(escTriggerOn); }

    /** Returns {@code true} if --esc should only fire on explicit command. */
    public boolean isEscManual()   { return "manual".equalsIgnoreCase(escTriggerOn); }

    /**
     * Syntax coloring strategy for JML tokens:
     * <ul>
     *   <li>{@code "ast"} (default) — AST-based coloring when an attributed AST is
     *       available (no false positives for identifiers that share a JML keyword name),
     *       with regex fallback before the first {@code --check}.</li>
     *   <li>{@code "regex"} — always use the regex-based approach (instant, but may
     *       color non-JML identifiers that happen to match JML keywords).</li>
     * </ul>
     */
    public volatile String syntaxColoringStrategy = "ast";

    /** Returns {@code true} if the regex-only coloring strategy is selected. */
    public boolean isRegexColoring() { return "regex".equalsIgnoreCase(syntaxColoringStrategy); }

    /**
     * Which engine to use for ESC:
     * <ul>
     *   <li>{@code "subprocess"} (default) — spawn a fresh OpenJML process with {@code --esc}</li>
     *   <li>{@code "concurrent"} — call {@link org.openjml.IAPI#doESC} in-process on the cached AST
     *       from the last successful {@code --check}.  No re-typechecking; ESC attempts on methods
     *       are done concurrently according to the number of threads setting.
     *       Falls back to subprocess if no cached IAPI is available.</li>
     * </ul>
     */
    public volatile String escEngine = "subprocess";

    /** Returns {@code true} if the concurrent in-process doESC engine is selected. */
    public boolean isEscApiMode() { return "concurrent".equalsIgnoreCase(escEngine); }

    /**
     * Maximum number of concurrent doESC threads used by the {@code concurrent} engine.
     * Methods from different files run concurrently up to this limit;
     * methods within the same file are serialized (IAPI.doESC is not thread-safe per instance).
     */
    public volatile int escThreads = 5;

    /**
     * Fixed thread pool used by the {@code api} engine to run per-method doESC calls
     * concurrently.  {@code transient} so Gson never touches it.  Recreated by
     * {@link org.openjml.lsp.OpenJMLWorkspaceService} whenever {@link #escThreads}
     * is updated via a configuration change.
     */
    public transient java.util.concurrent.ExecutorService escPool =
            java.util.concurrent.Executors.newFixedThreadPool(5);

    /**
     * Output directory for {@code --rac}-compiled class files, passed as {@code -d}.
     * Relative paths are resolved against the workspace root.
     * {@code null} or empty means {@code rac-classes} in the workspace root.
     */
    public volatile String racOutputDir;

    /**
     * Path to a {@code .properties} file generated by the Eclipse plugin from
     * the Tab-2 ("OpenJML Tool Options") preference page.  Passed as
     * {@code --properties} <em>before</em> the user-supplied
     * {@link #propertiesFile} so that the user's workspace file can override
     * Eclipse preferences.
     *
     * <p>Set when the Eclipse plugin's {@code USE_PROPERTIES_FILE} flag is
     * {@code true} (the default).  {@code null} or empty means no generated
     * file is available.
     */
    public volatile String generatedPropertiesFile;

    /**
     * Flat list of openjml command-line arguments built from the Tab-2
     * ("OpenJML Tool Options") preference page.  Prepended to the argument
     * list for every tool invocation.
     *
     * <p>Set when the Eclipse plugin's {@code USE_PROPERTIES_FILE} flag is
     * {@code false}.  {@code null} or empty means no extra args.
     */
    public volatile java.util.List<String> toolArgs;

    /**
     * No-arg constructor.  Used by Gson deserialization (initializationOptions /
     * didChangeConfiguration) and by test code that creates default settings.
     */
    public OpenJMLSettings() {}

    /**
     * Copy constructor.  Creates a shallow copy of {@code src} suitable for
     * per-invocation path overrides.  The {@link #escPool} is shared (not
     * recreated) so the copy participates in the same thread pool.
     */
    public OpenJMLSettings(OpenJMLSettings src) {
        this.propertiesFile          = src.propertiesFile;
        this.specsPath               = src.specsPath;
        this.solversPath             = src.solversPath;
        this.sourcePath              = src.sourcePath;
        this.workspaceFolderPaths    = src.workspaceFolderPaths;
        this.classPath               = src.classPath;
        this.useIntegratedOutline    = src.useIntegratedOutline;
        this.checkTriggerOn          = src.checkTriggerOn;
        this.escTriggerOn            = src.escTriggerOn;
        this.syntaxColoringStrategy  = src.syntaxColoringStrategy;
        this.escEngine               = src.escEngine;
        this.escThreads              = src.escThreads;
        this.escPool                 = src.escPool;   // share the pool
        this.racOutputDir            = src.racOutputDir;
        this.generatedPropertiesFile = src.generatedPropertiesFile;
        this.toolArgs                = src.toolArgs;
    }
}
