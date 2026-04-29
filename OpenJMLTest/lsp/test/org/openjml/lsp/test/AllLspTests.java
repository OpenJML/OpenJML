package org.openjml.lsp.test;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * JUnit 4 test suite that aggregates all LSP server tests.
 *
 * <h3>How to add a new test class</h3>
 * <ul>
 *   <li><b>Fast test</b> (pure logic, no ESC, &lt;5 s): add to {@link FastTests} only —
 *       this suite picks it up automatically via the {@code FastTests.class} entry below.</li>
 *   <li><b>Slow test</b> (starts the LSP server, runs ESC, or uses disk files):
 *       add here AND add a separate entry to {@code TEST_CLASSES} in the
 *       {@code lsp/Makefile} so it gets its own JVM process.</li>
 * </ul>
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    // ---- Fast tests (all in one JVM via FastTests suite) ----
    FastTests.class,

    // ---- Slow tests (each runs in its own JVM via the Makefile) ----
    DiagnosticsTest.class,
    EscStatusTest.class,
    MultiFileEscTest.class,
    EscDirWithContextTest.class,
    CommandDispatchTest.class,
    DocumentLifecycleTest.class,
    DefinitionFinderJmlTest.class,
    ReferenceFinderJmlTest.class,
    RenameTest1.class,
    RenameTest2.class,
    RenameTest3.class,
    RenameTest4.class,
    RenameJmlTest.class,
    RenameJmlTest2.class,
    RenameMethodAndClassTest.class,
    RenameProtocolTest.class,
    MethodAndClassTest.class,
    DocumentSymbolTest.class,
    DocumentSymbolProtocolTest.class,
    DoEscTest.class,
    EscCancellationTest.class,
    ConcurrentEscTest.class,
    CheckRunnerEscAndRacTest.class,
    PropertiesFileOptionsTest.class,
    ToolOptionsTest.class,
    RacTest.class,
    CodeLensAndStatusTest.class,
    HoverTest.class,
    RenamePreflightTest.class,
    DebouncingAndCancellationTest.class,
    BatchAndWatchedFilesTest.class,
    WatchedFilesHandlerTest.class,
    IncrementalSyncProtocolTest.class,
    MultiProjectTest.class,
    SplitEscTest.class,
    WorkspaceIndexTest.class,
    DocumentHighlightTest.class,
    ModelMethodEscTest.class,
    MultiClassEscTest.class,
    LauncherIntegrationTest.class,
    PerMethodEscStatusTest.class,
    JmlCompanionSemanticTokensTest.class,
    GoToDefinitionCrossFileTest.class,
    LanguageServerLifecycleTest.class,
    CheckRunnerEscContextTest.class,
    LegacyEscSmokeTest.class,
    SymlinkWorkspaceTest.class,
    EscSessionGenTest.class,
    SymbolsForProjectTest.class,
    EscPerMethodMarkerTest.class,
    EscAtLineTest.class,
    EscInvocationVariantsTest.class,
    ClearAndReescTest.class,
    ClearMarkersTest.class,
    DidCloseTest.class,
    WorkspaceFoldersTest.class,
})
public class AllLspTests {}
