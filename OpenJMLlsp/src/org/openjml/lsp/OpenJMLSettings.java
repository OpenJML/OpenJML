package org.openjml.lsp;

import java.util.List;
import java.util.stream.Collectors;

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
     * The project ID used for the synthesized single-project entry created for
     * generic LSP clients (e.g. VS Code) that do not send an explicit
     * {@code projects} array.  The same constant is used by
     * {@code didChangeWorkspaceFolders} to identify and update this entry.
     */
    public static final String WORKSPACE_PROJECT_ID = "__workspace__";

    // -----------------------------------------------------------------------
    // Per-project configuration
    // -----------------------------------------------------------------------

    /**
     * Per-project configuration sent by the Eclipse plugin in
     * {@code didChangeConfiguration}.  Each entry corresponds to one open
     * Eclipse project that has the JML nature.
     *
     * <p>When this list is non-empty, the server maintains a per-project
     * settings registry and ignores the global {@link #sourcePath},
     * {@link #classPath} fields for source-path construction
     * (those fields are irrelevant for multi-project clients).
     *
     * <p>Single-project clients (e.g. VS Code) do not send this list and
     * continue to use the global fields.
     */
    public volatile List<ProjectConfig> projects;

    /**
     * Per-project filesystem root paths.
     *
     * <p>This field is set on <em>per-project</em> {@link OpenJMLSettings}
     * instances built by
     * {@link OpenJMLTextDocumentService#updateProjectSettings} — it is NOT
     * serialized by the Eclipse plugin.  It holds only this project's own
     * source folders (not dependency sources) so
     * {@link OpenJMLTextDocumentService#settingsForUri} can map a file URI to
     * the correct project.
     */
    public volatile List<String> rootPaths;

    /**
     * Per-project configuration record.
     *
     * <p>Sent inside the {@link OpenJMLSettings#projects} list by the Eclipse
     * plugin.  All path fields use the OS path separator (colon on Unix,
     * semicolon on Windows).
     */
    public static class ProjectConfig {
        /** Eclipse {@code IProject.getName()} — used as the lookup key. */
        public String id;

        /**
         * This project's source folders plus its transitive dependency source
         * folders, passed as {@code -sourcepath}.
         */
        public String sourcePath;

        /**
         * Classpath: transitive dependency output directories plus any
         * user-configured classpath preference.
         */
        public String classPath;

        /**
         * OpenJML specs path ({@code --specs-path}).  Per-project because the
         * default is derived from {@link #sourcePath}.
         */
        public String specsPath;

        /**
         * Output directory for RAC-compiled {@code .class} files
         * ({@code -d}).  Set to the Eclipse project's JDT output folder.
         */
        public String outputDir;

        /**
         * This project's own source folders only (not dependency sources).
         * Used by the server to map a file URI to its owning project.
         */
        public List<String> rootPaths;
    }

    // -----------------------------------------------------------------------
    // Global / single-project fields
    // -----------------------------------------------------------------------

    /**
     * Project-independent OpenJML command-line options prepended verbatim to
     * every tool invocation.  Clients use this to pass {@code --properties},
     * warning flags, prover settings, or any other OpenJML option that applies
     * uniformly across all projects in the workspace.
     *
     * <p>For example, to point OpenJML at a properties file:
     * {@code ["--properties", "/path/to/openjml.properties"]}.
     * Alternatively, individual options such as {@code ["--nullable-by-default"]}
     * may be listed directly.
     *
     * <p>Project-dependent settings (source path, class path, specs path) are kept
     * in the named fields below and are appended after {@code toolOptions}.
     */
    public volatile List<String> toolOptions;

    /**
     * Path to the OpenJML specs directory, passed as {@code --specs-path}.
     * {@code null} or empty means use the server's default.
     */
    public volatile String specsPath;

    /**
     * Source root(s) for resolving cross-file references, passed as
     * {@code -sourcepath}.  Colon-separated on Unix, semicolon on Windows.
     * Used only by single-project clients (VS Code).  Ignored when
     * {@link #projects} is non-empty.
     */
    public volatile String sourcePath;

    /**
     * Returns the effective list of root paths for JML work.
     *
     * <p>Priority order:
     * <ol>
     *   <li>Global settings with {@link #projects} list — union of all projects' rootPaths.</li>
     *   <li>Per-project settings object — {@link #rootPaths} (this project's own source folders).</li>
     * </ol>
     */
    public List<String> effectiveRoots() {
        if (projects != null && !projects.isEmpty()) {
            return projects.stream()
                    .filter(p -> p.rootPaths != null)
                    .flatMap(p -> p.rootPaths.stream())
                    .filter(r -> r != null && !r.isBlank())
                    .collect(Collectors.toList());
        }
        // Per-project settings object (built by updateProjectSettings).
        if (rootPaths != null && !rootPaths.isEmpty())
            return rootPaths;
        return List.of();
    }

    /**
     * Classpath for pre-compiled dependencies, passed as {@code -classpath}.
     * Colon-separated on Unix, semicolon on Windows.
     * Used only by single-project clients; ignored when {@link #projects} is non-empty.
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
     *   <li>{@code "edit"} (default) — check on every document change (debounced),
     *       on open, and on save</li>
     *   <li>{@code "save"} — check on open and on save, but not on change</li>
     *   <li>{@code "manual"} — never automatic; only via the explicit
     *       {@code openjml.checkJml} command.  Intended for codebases where
     *       checking is slow or where automatic checks cause problems.</li>
     * </ul>
     */
    public volatile String checkTriggerOn = "edit";

    /**
     * When to run the {@code --esc} pass:
     * <ul>
     *   <li>{@code "manual"} (default) — only on explicit command ({@code openjml.runEsc})</li>
     *   <li>{@code "save"} — on every save</li>
     * </ul>
     */
    public volatile String escTriggerOn = "manual";

    /** Returns {@code true} if --check should fire on every edit (debounced). */
    public boolean isCheckOnEdit()  { return "edit".equalsIgnoreCase(checkTriggerOn); }

    /** Returns {@code true} if --check should fire on save (and open). */
    public boolean isCheckOnSave()  { return "save".equalsIgnoreCase(checkTriggerOn); }

    /** Returns {@code true} if --check should only fire on explicit command. */
    public boolean isCheckManual()  { return "manual".equalsIgnoreCase(checkTriggerOn); }

    /** Returns {@code true} if --esc should fire on save. */
    public boolean isEscOnSave()   { return "save".equalsIgnoreCase(escTriggerOn); }

    /** Returns {@code true} if --esc should only fire on explicit command. */
    public boolean isEscManual()   { return "manual".equalsIgnoreCase(escTriggerOn); }

    /**
     * Syntax coloring scope:
     * <ul>
     *   <li>{@code "preserve Java coloring"} (default) — emit tokens only inside JML annotation
     *       context; Java code outside JML comments is left to the Java language server.</li>
     *   <li>{@code "overwrite Java coloring"} — emit tokens for all Java and JML constructs;
     *       OpenJML's colors replace whatever the Java language server produced.</li>
     * </ul>
     */
    public volatile String syntaxColoringScope = "preserve Java coloring";

    /** Returns {@code true} when OpenJML should emit tokens for all Java constructs. */
    public boolean isOverwriteJavaColoring() {
        return "overwrite Java coloring".equalsIgnoreCase(syntaxColoringScope);
    }

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
     *   <li>{@code "fresh"} (default) — spawn a fresh OpenJML process with {@code --esc}</li>
     *   <li>{@code "concurrent"} — call {@link org.openjml.IAPI#doESC} in-process on the cached AST
     *       from the last successful {@code --check}.  No re-typechecking; ESC attempts on methods
     *       are done concurrently according to the number of threads setting.
     *       Falls back to the fresh engine if no cached IAPI is available.</li>
     * </ul>
     */
    public volatile String escEngine = "fresh";

    /** Returns {@code true} if the concurrent in-process doESC engine is selected. */
    public boolean isEscApiMode() { return "concurrent".equalsIgnoreCase(escEngine); }

    /**
     * Maximum number of concurrent ESC tasks in {@link #escPool}.  Governs
     * parallelism for all ESC modes: per-method {@code doESC} calls in the
     * {@code concurrent} engine, and per-file or per-method subprocess invocations
     * in the {@code fresh} engine when using split-by-file or split-by-method.
     */
    public volatile int escThreads = 5;

    /**
     * Fixed thread pool shared by all ESC execution paths.  {@code transient} so
     * Gson never touches it.  Recreated by
     * {@link org.openjml.lsp.OpenJMLWorkspaceService} whenever {@link #escThreads}
     * is updated via a configuration change.
     */
    public transient java.util.concurrent.ExecutorService escPool =
            java.util.concurrent.Executors.newFixedThreadPool(5);

    /**
     * When {@code true} (default), the server advertises
     * {@code TextDocumentSyncKind.Incremental} and applies each
     * {@code textDocument/didChange} event as a set of ranged edits rather than
     * replacing the full document string.  Set to {@code false} to revert to
     * full-document sync (useful for debugging or performance comparison).
     */
    public volatile boolean incrementalSync = true;

    /**
     * Output directory for {@code --rac}-compiled class files, passed as {@code -d}.
     * Relative paths are resolved against the workspace root.
     * {@code null} or empty means {@code rac-classes} in the workspace root.
     * Used only by single-project clients; for Eclipse, outputDir is per-project
     * inside {@link ProjectConfig#outputDir}.
     */
    public volatile String racOutputDir;

    /**
     * Java-vs-JML-only master switch.
     * <ul>
     *   <li>{@code "full"} (default) — OpenJML emits all Java + JML capabilities
     *       (inlay hints, signature help, etc.).</li>
     *   <li>{@code "jml-only"} — suppress capabilities that duplicate a co-present
     *       Java language server (JDT, Red Hat Java, IntelliJ Java, etc.).</li>
     * </ul>
     * Individual capabilities check this setting and return empty results when it
     * is {@code "jml-only"}.  The value is also influenced by {@link #client}: for
     * known Java-capable clients the default shifts to {@code "jml-only"} unless
     * the user explicitly sets this field to {@code "full"}.
     *
     * @see #resolveDefaults()
     */
    public volatile String javaMode;   // null = unset by client; use resolveDefaults()

    /**
     * When {@code true}, the client understands the {@code $/openjml/actionMessage}
     * custom notification and the server will use it instead of {@code window/logMessage}
     * for advisory and error messages that may offer actions (e.g. "Open Preferences").
     *
     * <p>Capable clients set this to {@code true} in {@code initializationOptions}.
     * Generic clients omit it (defaults to {@code false}), and the server falls back
     * to plain {@code window/logMessage}.
     */
    public volatile boolean supportsActionMessages = false;

    /**
     * Known-client hint — lets the server tailor capability defaults without the
     * user having to set every flag manually.
     * <ul>
     *   <li>{@code "generic"} (default) — no assumptions; all capabilities enabled.</li>
     *   <li>{@code "eclipse-jdt"} — Eclipse with JDT active; default {@code javaMode}
     *       to {@code "jml-only"}.  The OpenJMLUI Eclipse plugin sets this automatically
     *       in its {@code initializationOptions}.</li>
     *   <li>{@code "vscode-java"} — VS Code with Red Hat Java extension; likewise.</li>
     *   <li>{@code "intellij"} — IntelliJ IDEA; likewise.</li>
     * </ul>
     */
    public volatile String client = "generic";

    /**
     * Return the effective {@code javaMode} after applying client-based defaults.
     * If {@link #javaMode} was explicitly set by the client, that value is returned
     * directly.  Otherwise the mode is inferred from {@link #client}:
     * {@code "eclipse-jdt"}, {@code "vscode-java"}, and {@code "intellij"} default
     * to {@code "jml-only"}; everything else defaults to {@code "full"}.
     */
    public String effectiveJavaMode() {
        if (javaMode != null && !javaMode.isEmpty()) return javaMode;
        if ("eclipse-jdt".equals(client) || "vscode-java".equals(client)
                || "intellij".equals(client)) return "jml-only";
        return "full";
    }

    /** Returns {@code true} when Java-overlapping capabilities should be suppressed. */
    public boolean isJmlOnly() { return "jml-only".equals(effectiveJavaMode()); }

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
        this.toolOptions             = src.toolOptions;
        this.specsPath               = src.specsPath;

        this.sourcePath              = src.sourcePath;
        this.rootPaths               = src.rootPaths;
        this.classPath               = src.classPath;
        this.useIntegratedOutline    = src.useIntegratedOutline;
        this.checkTriggerOn          = src.checkTriggerOn;
        this.escTriggerOn            = src.escTriggerOn;
        this.syntaxColoringScope     = src.syntaxColoringScope;
        this.syntaxColoringStrategy  = src.syntaxColoringStrategy;
        this.escEngine               = src.escEngine;
        this.escThreads              = src.escThreads;
        this.escPool                 = src.escPool;   // share the pool
        this.racOutputDir            = src.racOutputDir;
        this.incrementalSync         = src.incrementalSync;
        this.javaMode                = src.javaMode;
        this.client                  = src.client;
        // projects/rootPaths are not copied — per-project instances don't nest
    }
}
