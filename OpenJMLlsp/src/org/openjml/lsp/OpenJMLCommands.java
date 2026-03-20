package org.openjml.lsp;

/**
 * LSP {@code workspace/executeCommand} identifiers for the OpenJML language server.
 *
 * <p>These strings are shared constants used by all clients — the VS Code extension,
 * the Eclipse plugin, and the server itself.  They must match the command IDs declared
 * in the VS Code extension's {@code package.json} and in the Eclipse plugin's
 * {@code plugin.xml}.
 */
public final class OpenJMLCommands {

    /** Full-file ESC: {@code openjml.runEsc}. */
    public static final String RUN_ESC             = "openjml.runEsc";

    /**
     * Per-method ESC: {@code openjml.runEscForMethod}.
     *
     * <p>Arguments: {@code [uri, methodFqn]} where {@code methodFqn} is
     * {@code pkg.Class.method} as produced by {@link JavaSourceScanner#methodFqn}.
     */
    public static final String RUN_ESC_FOR_METHOD  = "openjml.runEscForMethod";

    /**
     * Multi-path ESC: {@code openjml.runEscDir}.
     *
     * <p>Arguments: one or more file-system paths (files or directories).
     * Each path is processed recursively via OpenJML's {@code --dirs} flag.
     */
    public static final String RUN_ESC_DIR         = "openjml.runEscDir";

    /**
     * Focus notification: {@code openjml.focusFile}.
     *
     * <p>Sent by a client when the user switches focus to an already-open Java file.
     * Triggers a {@code --check} recheck so stale diagnostics from fixed dependencies
     * are cleared.
     */
    public static final String FOCUS_FILE          = "openjml.focusFile";

    /**
     * RAC compile: {@code openjml.runRac}.
     *
     * <p>Arguments: {@code [uri]} or {@code [uri, outputDir]}.  When {@code outputDir}
     * is supplied (e.g. the Eclipse project's JDT output folder), RAC class files are
     * written there; otherwise the server uses the {@code openjml.racOutputDir} setting.
     */
    public static final String RUN_RAC             = "openjml.runRac";

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
     * restarts as if the server had just started — re-checking open files and
     * re-indexing the workspace.  Takes no arguments.
     */
    public static final String CLEAR_AND_REINDEX   = "openjml.clearAndReindex";

    /**
     * Clear markers: {@code openjml.clearMarkers}.
     *
     * <p>Removes all OpenJML diagnostic markers from the client without scheduling
     * any new checks.  Useful when markers are stale and the user wants a clean slate
     * without a full reindex.  Takes no arguments.
     */
    public static final String CLEAR_MARKERS       = "openjml.clearMarkers";

    private OpenJMLCommands() {}
}
