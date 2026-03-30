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
    DefinitionFinderJmlTest.class,
    ReferenceFinderTest.class,
    ReferenceFinderJmlTest.class,
    RenameTest1.class,
    RenameTest2.class,
    RenameTest3.class,
    RenameJmlTest.class,
    MethodAndClassTest.class,
    SemanticTokensTest.class,
    DocumentSymbolTest.class,
    FoldingRangeTest.class,
    DoEscTest.class,
    PropertiesFileOptionsTest.class,
})
public class AllLspTests {}
