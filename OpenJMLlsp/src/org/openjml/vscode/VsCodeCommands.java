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

    private VsCodeCommands() {}
}
