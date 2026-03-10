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
     * Focus notification: sent by the extension when the user switches focus to
     * an already-open Java file.  Triggers a --check recheck so stale diagnostics
     * from fixed dependencies are cleared.
     */
    public static final String FOCUS_FILE = "openjml.focusFile";

    private VsCodeCommands() {}
}
