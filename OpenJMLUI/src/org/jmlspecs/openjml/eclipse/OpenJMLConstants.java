/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

/**
 * String constants used by the OpenJML Eclipse plugin that must agree with
 * values declared in other artifacts.
 *
 * <p><b>plugin.xml synchronization.</b>  Many constants here duplicate literal
 * strings that appear in {@code plugin.xml} because Java code and XML
 * extension declarations cannot share the same source.  Both places must be
 * updated together whenever a constant changes; each constant's Javadoc
 * identifies its counterpart element in {@code plugin.xml}.
 *
 * <p><b>OpenJMLlsp synchronization.</b>  Constants for LSP command names and
 * diagnostic source tags mirror constants defined in the separate
 * {@code OpenJMLlsp} bundle ({@code org.openjml.lsp}).  Because that bundle is
 * not a compile-time dependency of this bundle, both copies must be kept in
 * sync manually; each constant's Javadoc names its counterpart.
 */
public final class OpenJMLConstants {

    // -----------------------------------------------------------------------
    // Language-server identity
    // -----------------------------------------------------------------------

    /**
     * OpenJML language-server ID as registered in the
     * {@code org.eclipse.lsp4e.languageServer} extension point.
     *
     * <p><b>plugin.xml sync</b>: {@code <languageServer id="...">}
     * in the {@code org.eclipse.lsp4e.languageServer} extension.
     */
    public static final String SERVER_ID = "org.jmlspecs.openjml.lsp.server";

    /**
     * Eclipse marker type created by LSP4E for every diagnostic received from
     * a language server.  OpenJML's custom marker types extend this type.
     *
     * <p>This is an LSP4E framework constant, not an OpenJML-defined one.
     * It is the supertype of {@link #JML_PROBLEM_MARKER}.
     */
    public static final String LSP4E_MARKER_TYPE = "org.eclipse.lsp4e.diagnostic";

    // -----------------------------------------------------------------------
    // Marker type IDs (must match plugin.xml markers extensions)
    // -----------------------------------------------------------------------

    /**
     * Eclipse marker type for JML type-check and syntax-check diagnostics.
     *
     * <p>The fully-qualified ID is the bundle symbolic name
     * ({@code org.openjml.OpenJMLUI}) plus the extension {@code id}
     * attribute ({@code JMLProblem}).
     *
     * <p><b>plugin.xml sync</b>:
     * {@code <extension id="JMLProblem" point="org.eclipse.core.resources.markers">}.
     */
    public static final String JML_PROBLEM_MARKER = "org.openjml.OpenJMLUI.JMLProblem";

    /**
     * Eclipse marker type for ESC (Extended Static Checking) proof-result
     * diagnostics.  Created directly by {@link OpenJMLLanguageClient}; managed
     * independently of {@link #JML_PROBLEM_MARKER}.
     *
     * <p><b>plugin.xml sync</b>:
     * {@code <extension id="JMLESCProblem" point="org.eclipse.core.resources.markers">}.
     */
    public static final String JML_ESC_MARKER = "org.openjml.OpenJMLUI.JMLESCProblem";

    // -----------------------------------------------------------------------
    // Diagnostic source tags (must match DiagnosticConverter in OpenJMLlsp)
    // -----------------------------------------------------------------------

    /**
     * LSP {@code Diagnostic.source} value stamped on every diagnostic produced
     * by a {@code --check} (JML type-check / syntax-check) pass.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code DiagnosticConverter.SOURCE_CHECK}
     * in the {@code OpenJMLlsp} bundle.  Both copies must be identical.
     */
    public static final String SOURCE_CHECK = "openjml.check";

    /**
     * LSP {@code Diagnostic.source} value stamped on every diagnostic produced
     * by a {@code --esc} (Extended Static Checking) pass.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code DiagnosticConverter.SOURCE_ESC}
     * in the {@code OpenJMLlsp} bundle.  Both copies must be identical.
     */
    public static final String SOURCE_ESC = "openjml.esc";

    // -----------------------------------------------------------------------
    // LSP workspace/executeCommand names
    // (must match OpenJMLCommands in OpenJMLlsp AND plugin.xml command handlers)
    // -----------------------------------------------------------------------

    /**
     * JML type-check command sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.CHECK_JML}.
     * <p><b>plugin.xml sync</b>: {@code commandId} of the {@code checkJML} handler.
     */
    public static final String CMD_CHECK_JML = "openjml.checkJML";

    /**
     * Multi-target ESC command sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.RUN_ESC}.
     */
    public static final String CMD_RUN_ESC = "openjml.runEsc";

    /**
     * Per-method ESC command sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.RUN_ESC_FOR_METHOD}.
     */
    public static final String CMD_RUN_ESC_FOR_METHOD = "openjml.runEscForMethod";

    /**
     * Split-by-file ESC command sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.RUN_ESC_SPLIT_BY_FILE}.
     */
    public static final String CMD_RUN_ESC_SPLIT_BY_FILE = "openjml.runEscSplitByFile";

    /**
     * Split-by-method ESC command sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.RUN_ESC_SPLIT_BY_METHOD}.
     */
    public static final String CMD_RUN_ESC_SPLIT_BY_METHOD = "openjml.runEscSplitByMethod";

    /**
     * Multi-target RAC compile command sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.RUN_RAC}.
     */
    public static final String CMD_RUN_RAC = "openjml.runRac";

    /**
     * Clear-and-reindex command sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.CLEAR_AND_REINDEX}.
     */
    public static final String CMD_CLEAR_AND_REINDEX = "openjml.clearAndReindex";

    /**
     * Clear-markers command sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.CLEAR_MARKERS}.
     */
    public static final String CMD_CLEAR_MARKERS = "openjml.clearMarkers";

    /**
     * Cancel-ESC command sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.CANCEL_ESC}.
     */
    public static final String CMD_CANCEL_ESC = "openjml.cancelEsc";

    /**
     * Get-running-ESC-tasks query sent via {@code workspace/executeCommand}.
     * Returns a {@code List<String>} of file URIs currently being verified.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.GET_RUNNING_ESC_TASKS}.
     */
    public static final String CMD_GET_RUNNING_ESC_TASKS = "openjml.getRunningEscTasks";

    /**
     * Focus-file notification sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.FOCUS_FILE}.
     */
    public static final String CMD_FOCUS_FILE = "openjml.focusFile";

    /**
     * Index-project command sent via {@code workspace/executeCommand}.
     * Triggers a {@code --check} pass on all source directories of the
     * specified project to populate the declaration index.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.INDEX_PROJECT}.
     */
    public static final String CMD_INDEX_PROJECT = "openjml.indexProject";

    /**
     * Per-project symbol query sent via {@code workspace/executeCommand}.
     * Arguments: {@code [query, projectRoot]}.  Returns {@code List<SymbolInformation>}
     * restricted to files under {@code projectRoot}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.SYMBOLS_FOR_PROJECT}.
     */
    public static final String CMD_SYMBOLS_FOR_PROJECT = "openjml.symbolsForProject";

    /**
     * Semantic-tokens request sent via {@code workspace/executeCommand}.
     *
     * <p><b>OpenJMLlsp sync</b>: {@code OpenJMLCommands.GET_SEMANTIC_TOKENS}.
     */
    public static final String CMD_GET_SEMANTIC_TOKENS = "openjml.getSemanticTokens";

    // -----------------------------------------------------------------------
    // Eclipse UI command IDs (must match plugin.xml command definitions)
    // These are Eclipse workbench command IDs, not LSP executeCommand names.
    // -----------------------------------------------------------------------

    /**
     * Eclipse UI command ID for the OpenJML Find Declaration action.
     *
     * <p><b>plugin.xml sync</b>: {@code <command id="...">} in the
     * {@code org.eclipse.ui.commands} extension.
     */
    public static final String CMD_UI_FIND_DECLARATION =
            "org.openjml.eclipse.commands.findDeclaration";

    /**
     * Eclipse UI command ID for the OpenJML Find References action.
     *
     * <p><b>plugin.xml sync</b>: {@code <command id="...">} in the
     * {@code org.eclipse.ui.commands} extension.
     */
    public static final String CMD_UI_FIND_REFERENCES =
            "org.openjml.eclipse.commands.findReferences";

    /**
     * Eclipse UI command ID for the OpenJML Rename action.
     *
     * <p><b>plugin.xml sync</b>: {@code <command id="...">} in the
     * {@code org.eclipse.ui.commands} extension.
     */
    public static final String CMD_UI_RENAME =
            "org.openjml.eclipse.commands.rename";

    /**
     * Eclipse UI command ID for the OpenJML Find All Declarations action.
     *
     * <p><b>plugin.xml sync</b>: {@code <command id="...">} in the
     * {@code org.eclipse.ui.commands} extension.
     */
    public static final String CMD_UI_FIND_ALL_DECLARATIONS =
            "org.openjml.eclipse.commands.findAllDeclarations";

    /**
     * Eclipse UI command ID for the OpenJML Index Project action.
     *
     * <p><b>plugin.xml sync</b>: {@code <command id="...">} in the
     * {@code org.eclipse.ui.commands} extension.
     */
    public static final String CMD_UI_INDEX_PROJECT =
            "org.jmlspecs.openjml.commands.indexProject";

    // -----------------------------------------------------------------------
    // Decorator ID
    // -----------------------------------------------------------------------

    /**
     * Eclipse decorator ID for the JML overlay icon shown on JML-natured
     * projects in the Package/Project Explorer.
     *
     * <p><b>plugin.xml sync</b>: {@code <decorator id="...">} in the
     * {@code org.eclipse.ui.decorators} extension.
     */
    public static final String DECORATOR_ID = "org.openjml.OpenJMLUI.JMLDecoration";

    // -----------------------------------------------------------------------
    // System-property keys
    // -----------------------------------------------------------------------

    /**
     * JVM system property that overrides the path to the {@code openjml-lsp}
     * executable.  When set, {@code OpenJMLStreamConnectionProvider} uses this
     * path instead of searching the Eclipse installation directory.
     *
     * <p>Typically set by the Makefile when running GUI tests:
     * {@code -Dopenjml.lsp.server.path=/path/to/openjml-lsp}.
     */
    public static final String LSP_SERVER_PATH_PROPERTY = "openjml.lsp.server.path";

    private OpenJMLConstants() {}
}
