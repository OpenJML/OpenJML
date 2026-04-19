package org.openjml.lsp;

/**
 * LSP {@code workspace/executeCommand} identifiers for the OpenJML language server.
 *
 * <p>These strings are shared constants used by all clients -- the VS Code extension,
 * the Eclipse plugin, and the server itself.
 *
 * <p><b>Unified argument encoding.</b>  All commands share a common prefix:
 * <pre>
 *   args[0]  projectId  -- registered project name, or "" for global/single-project settings
 *   args[1+]            -- command-specific paths / URIs
 * </pre>
 * Path configuration ({@code sourcePath}, {@code classPath}, {@code specsPath}, etc.) is
 * sent once at initialization via {@code initializationOptions} and updated via
 * {@code workspace/didChangeConfiguration}; it is not repeated in command arguments.
 */
public final class OpenJMLCommands {

    /**
     * JML type-check: {@code openjml.checkJML}.
     *
     * <p>Arguments: {@code [projectId, path1, path2, ...]}.
     * {@code path1..N} are OS file-system paths (files or directories) passed to
     * {@code --check --dirs}.
     */
    public static final String CHECK_JML          = "openjml.checkJML";

    /**
     * Multi-target ESC: {@code openjml.runEsc}.
     *
     * <p>Arguments: {@code [projectId, path1, path2, ...]}.
     * {@code path1..N} are OS file-system paths (files or directories) passed to
     * {@code --esc --dirs}.
     */
    public static final String RUN_ESC            = "openjml.runEsc";

    /**
     * Per-method ESC: {@code openjml.runEscForMethod}.
     *
     * <p>Standard format: {@code [projectId, uri, methodFqn]}.
     * Code-lens format (detected automatically): {@code [uri, methodFqn]} where
     * {@code uri} starts with {@code file://}.
     * {@code methodFqn} is the unique per-project method name from
     * {@link JavaSourceScanner.MethodInfo#rawName()} (e.g. {@code pkg.Class.method(int,int)}).
     */
    public static final String RUN_ESC_FOR_METHOD = "openjml.runEscForMethod";

    /**
     * Split-by-file ESC: {@code openjml.runEscSplitByFile}.
     *
     * <p>Arguments: {@code [projectId, path1, path2, ...]}.
     * The server recursively walks each path for {@code .java} files and submits
     * each file as a separate task to the bounded ESC thread pool.
     */
    public static final String RUN_ESC_SPLIT_BY_FILE   = "openjml.runEscSplitByFile";

    /**
     * Split-by-method ESC: {@code openjml.runEscSplitByMethod}.
     *
     * <p>Arguments: {@code [projectId, path1, path2, ...]}.
     * The server expands paths to {@code .java} files, discovers methods in each
     * (AST cache preferred, regex fallback), and submits each method as a separate
     * task to the bounded ESC thread pool.
     */
    public static final String RUN_ESC_SPLIT_BY_METHOD = "openjml.runEscSplitByMethod";

    /**
     * Multi-target RAC: {@code openjml.runRac}.
     *
     * <p>Arguments: {@code [projectId, path1, path2, ...]}.
     * {@code path1..N} are OS file-system paths (files or directories) passed to
     * {@code --rac --dirs}.  The output directory for compiled class files is taken
     * from the project's {@code ProjectConfig.outputDir}.
     */
    public static final String RUN_RAC            = "openjml.runRac";

    /**
     * Focus notification: {@code openjml.focusFile}.
     *
     * <p>Sent by a client when the user switches focus to an already-open Java file.
     * Triggers a {@code --check} recheck so stale diagnostics from fixed dependencies
     * are cleared.
     */
    public static final String FOCUS_FILE         = "openjml.focusFile";

    /**
     * Semantic tokens request: {@code openjml.getSemanticTokens}.
     *
     * <p>Used by the VS Code extension's directly-registered
     * {@code DocumentSemanticTokensProvider} to obtain JML token data without going
     * through the standard LSP semantic-tokens protocol (which would conflict with the
     * Red Hat Java extension).
     */
    public static final String GET_SEMANTIC_TOKENS = "openjml.getSemanticTokens";

    /**
     * Clear-and-reindex: {@code openjml.clearAndReindex}.
     *
     * <p>Clears all server-side caches (AST cache, diagnostics, ESC status) and
     * restarts as if the server had just started -- re-checking open files and
     * re-indexing the workspace.  Takes no arguments.
     */
    public static final String CLEAR_AND_REINDEX  = "openjml.clearAndReindex";

    /**
     * Clear markers: {@code openjml.clearMarkers}.
     *
     * <p>Removes all OpenJML diagnostic markers from the client without scheduling
     * any new checks.  Useful when markers are stale and the user wants a clean slate
     * without a full reindex.  Takes no arguments.
     */
    public static final String CLEAR_MARKERS      = "openjml.clearMarkers";

    /**
     * Cancel ESC: {@code openjml.cancelEsc}.
     *
     * <p>Cancels a specific running ESC task or all running ESC tasks.
     * Also kills the in-progress SMT solver process so the ESC thread is
     * unblocked immediately.
     *
     * <p>Arguments: {@code [target]} (optional).  Granularity:
     * <ul>
     *   <li>absent or empty — cancel all per-file and per-method tasks.</li>
     *   <li>bare URI (no {@code #}) — cancel the whole-file run for that URI.</li>
     *   <li>{@code "uri#methodName"} — cancel only that specific method's run.</li>
     * </ul>
     */
    public static final String CANCEL_ESC         = "openjml.cancelEsc";

    /**
     * Abort current proof: {@code openjml.abortCurrentProof}.
     *
     * <p>Aborts only the currently-running method proof, then allows the ESC loop
     * to continue with the next method.  Unlike {@link #CANCEL_ESC}, this does
     * not prevent subsequent methods from being proved.
     *
     * <p>Arguments: {@code [target]} (optional).  Same granularity as
     * {@link #CANCEL_ESC}.
     */
    public static final String ABORT_CURRENT_PROOF = "openjml.abortCurrentProof";

    /**
     * Get running ESC tasks: {@code openjml.getRunningEscTasks}.
     *
     * <p>Returns a {@code List<String>} of task keys for all currently-running
     * ESC tasks.  Whole-file runs are identified by bare URI; per-method runs
     * use the format {@code "uri#methodName"}.
     * Intended for use by the client to populate a cancel dialog before calling
     * {@link #CANCEL_ESC}.
     *
     * <p>Arguments: none.
     */
    public static final String GET_RUNNING_ESC_TASKS = "openjml.getRunningEscTasks";

    /**
     * Index project: {@code openjml.indexProject}.
     *
     * <p>Triggers a {@code --check} pass on all source directories of the
     * specified project (or all configured projects when no project ID is given),
     * rebuilding the declaration index without clearing existing diagnostics or
     * the AST cache.  Use this to populate the declaration index for
     * {@code workspace/symbol} ("Find All Declarations") before the user has
     * manually opened each file.
     *
     * <p>Arguments: {@code [projectId]} (optional).  When {@code projectId}
     * matches a project registered via the {@code projects} settings array, only
     * that project's source directories are indexed.  An absent or empty
     * {@code projectId} indexes all configured projects.
     */
    public static final String INDEX_PROJECT = "openjml.indexProject";

    /**
     * Per-project symbol query: {@code openjml.symbolsForProject}.
     *
     * <p>Returns the same data as {@code workspace/symbol} but filtered to a
     * single project, identified by its file-system root path.  This avoids the
     * cross-project leakage that occurs when multiple projects are indexed and the
     * client-side URI comparison is unreliable.
     *
     * <p>Arguments: {@code [query, projectId]}.
     * <ul>
     *   <li>{@code query} — case-insensitive substring to match; empty = return all.</li>
     *   <li>{@code projectId} — project identifier from the {@code projects} settings array
     *       (e.g. {@code IProject.getName()} in the Eclipse plugin).  When absent or empty,
     *       symbols from all projects are returned.  An unknown ID is reported as an error.</li>
     * </ul>
     *
     * <p>Returns a {@code List<SymbolInformation>} serialized as JSON.
     */
    public static final String SYMBOLS_FOR_PROJECT = "openjml.symbolsForProject";

    private OpenJMLCommands() {}
}
