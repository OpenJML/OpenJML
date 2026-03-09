package org.openjml.lsp.test;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * JUnit 4 test suite that aggregates all LSP server tests.
 *
 * <p>Add new test classes here as they are created — the Makefile runs only
 * this suite, so listing them here is the single point of registration.
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    DiagnosticsTest.class,
    EscStatusTest.class,
    MultiFileEscTest.class,
    LspProtocolTest.class,
    DefinitionFinderTest.class,
    ReferenceFinderTest.class,
    RenameTest.class,
})
public class AllLspTests {}
