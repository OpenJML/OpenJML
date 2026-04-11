package org.openjml.lsp;

/**
 * LSP {@code workspace/executeCommand} identifiers for the OpenJML language server.
 *
 * <p>These strings are shared constants used by all clients -- the VS Code extension,
 * the Eclipse plugin, and the server itself.
 *
 * <p><b>Unified argument encoding.</b>  All commands share a fixed 4-element prefix:
 * <pre>
 *   args[0]  sourcePath     -- OS path(s) for -sourcepath (empty = use server default)
 *   args[1]  classPath      -- OS path(s) for -classpath  (empty = use server default)
 *   args[2]  specsPath      -- path to OpenJML specs dir   (empty = use server default)
 *   args[3]  propertiesFile -- path to generated .properties file (empty = none)
 * </pre>
 * Command-specific arguments follow at position 4+.  Empty strings are used for
 * absent optional values so that positions are always fixed.
 */
public final class OpenJMLCommands {

    /**
     * JML type-check: {@code openjml.checkJML}.
     *
     * <p>Arguments: {@code [sourcePath, classPath, specsPath, propertiesFile, path1, path2, ...]}.
     * {@code path1..N} are OS file-system paths (files or directories) passed to
     * {@code --check --dirs}.
     */
    public static final String CHECK_JML          = "openjml.checkJML";

    /**
     * Multi-target ESC: {@code openjml.runEsc}.
     *
     * <p>Arguments: {@code [sourcePath, classPath, specsPath, propertiesFile, path1, path2, ...]}.
     * {@code path1..N} are OS file-system paths (files or directories) passed to
     * {@code --esc --dirs}.
     */
    public static final String RUN_ESC            = "openjml.runEsc";

    /**
     * Per-method ESC: {@code openjml.runEscForMethod}.
     *
     * <p>Arguments: {@code [sourcePath, classPath, specsPath, propertiesFile, uri, methodFqn]}.
     * {@code uri} is the document URI and {@code methodFqn} is {@code pkg.Class.method}
     * as produced by {@link JavaSourceScanner#methodFqn}.  An empty {@code methodFqn}
     * causes the server to ESC the whole file.
     */
    public static final String RUN_ESC_FOR_METHOD = "openjml.runEscForMethod";

    /**
     * Split-by-file ESC: {@code openjml.runEscSplitByFile}.
     *
     * <p>Arguments: same format as {@link #RUN_ESC}:
     * {@code [sourcePath, classPath, specsPath, propertiesFile, path1, path2, ...]}.
     * The server recursively walks each path for {@code .java} files and submits
     * each file as a separate task to the bounded ESC thread pool.
     */
    public static final String RUN_ESC_SPLIT_BY_FILE   = "openjml.runEscSplitByFile";

    /**
     * Split-by-method ESC: {@code openjml.runEscSplitByMethod}.
     *
     * <p>Arguments: same format as {@link #RUN_ESC}:
     * {@code [sourcePath, classPath, specsPath, propertiesFile, path1, path2, ...]}.
     * The server expands paths to {@code .java} files, discovers methods in each
     * (AST cache preferred, regex fallback), and submits each method as a separate
     * task to the bounded ESC thread pool.
     */
    public static final String RUN_ESC_SPLIT_BY_METHOD = "openjml.runEscSplitByMethod";

    /**
     * Multi-target RAC: {@code openjml.runRac}.
     *
     * <p>Arguments: {@code [sourcePath, classPath, specsPath, propertiesFile, outputDir, path1, path2, ...]}.
     * {@code outputDir} is the output directory for compiled class files (empty = use server default).
     * {@code path1..N} are OS file-system paths (files or directories) passed to
     * {@code --rac --dirs}.
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
     * <p>Arguments: {@code [query, projectRoot]}.
     * <ul>
     *   <li>{@code query} — exact case-sensitive symbol name; empty = return all.</li>
     *   <li>{@code projectRoot} — file-system path of the Eclipse project root
     *       ({@code IProject.getLocation().toOSString()}).  When absent or empty,
     *       symbols from all projects are returned.</li>
     * </ul>
     *
     * <p>Returns a {@code List<SymbolInformation>} serialized as JSON.
     */
    public static final String SYMBOLS_FOR_PROJECT = "openjml.symbolsForProject";

    private OpenJMLCommands() {}
}
