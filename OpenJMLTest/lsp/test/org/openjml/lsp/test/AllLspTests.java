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
    DefinitionFinderTest.class,
    DefinitionFinderJmlTest.class,
    ReferenceFinderTest.class,
    ReferenceFinderJmlTest.class,
    RenameTest1.class,
    RenameTest2.class,
    RenameTest3.class,
    RenameTest4.class,
    RenameJmlTest.class,
    RenameJmlTest2.class,
    MethodAndClassTest.class,
    DocumentSymbolTest.class,
    DoEscTest.class,
    EscCancellationTest.class,
    ConcurrentEscTest.class,
    FreshParallelEscTest.class,
    CheckRunnerEscAndRacTest.class,
    PropertiesFileOptionsTest.class,
    RacTest.class,
})
public class AllLspTests {}
