package org.openjml.vscode;

/**
 * VS Code command identifiers used by the OpenJML VS Code extension.
 *
 * <p>These strings must match the command IDs declared in the extension's
 * {@code package.json} contributes/commands section.  They are VS Code-specific
 * and must not appear in {@code org.openjml.lsp}.
 */
public final class VsCodeCommands {

    /** Full-file ESC command: {@code openjml.runEsc}. */
    public static final String RUN_ESC            = "openjml.runEsc";

    /** Per-method ESC command: {@code openjml.runEscForMethod}. */
    public static final String RUN_ESC_FOR_METHOD = "openjml.runEscForMethod";

    /**
     * Multi-path ESC command: {@code openjml.runEscDir}.
     *
     * <p>Arguments: one or more file-system paths (files or directories).
     * Each path is passed to OpenJML via {@code --dirs}; directory paths are
     * processed recursively.  This command is IDE-independent and is used
     * (at least) by the Eclipse plugin for project- and folder-level ESC.
     */
    public static final String RUN_ESC_DIR        = "openjml.runEscDir";

    /**
     * Focus notification: sent by the extension when the user switches focus to
     * an already-open Java file.  Triggers a --check recheck so stale diagnostics
     * from fixed dependencies are cleared.
     */
    public static final String FOCUS_FILE = "openjml.focusFile";

    /**
     * Semantic tokens request: sent by the extension's directly-registered
     * {@code DocumentSemanticTokensProvider}.  Returns the flat integer token
     * data for the given URI so VS Code can apply JML highlighting independently
     * of (and additively with) the Red Hat Java extension's semantic tokens.
     */
    public static final String GET_SEMANTIC_TOKENS = "openjml.getSemanticTokens";

    private VsCodeCommands() {}
}
