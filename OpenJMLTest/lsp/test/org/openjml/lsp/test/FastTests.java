package org.openjml.lsp.test;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * Combined suite for fast test classes (pure logic or light {@code --check} calls, each under ~5s).
 * Running them together in one JVM avoids per-class startup overhead.
 *
 * <p>This suite is referenced by {@link AllLspTests} as a single entry, so adding a
 * fast test here automatically makes it part of the full test run — no separate edit
 * to {@code AllLspTests} is needed.  Slow tests (ESC, protocol, disk-file tests) go
 * directly in {@code AllLspTests} and get a dedicated entry in the Makefile
 * {@code TEST_CLASSES}.
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    FoldingRangeTest.class,
    LspProtocolTest.class,
    SemanticTokensTest.class,
    SemanticTokensAstTest.class,
    SignatureHelpTest.class,
    JmlCompletionProviderTest.class,
    OpenJMLSettingsTest.class,
    DiagnosticConverterTest.class,
    CodeLensTest.class,
    CheckRunnerDirTest.class,
    WorkspaceSymbolTest.class,
    MockFileCornerCasesTest.class,
    LegacyDiskIOSmokeTest.class,
    JmlKeywordSyncTest.class,
    IncrementalSyncApplierTest.class,
    InlayHintsVarTypesTest.class,
    WatchedFilesTest.class,
    WatchedFilesHandlerTest.class,
    SuiteVsMakefileTest.class,
})
public class FastTests {}
