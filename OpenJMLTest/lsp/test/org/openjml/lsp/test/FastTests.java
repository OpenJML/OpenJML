package org.openjml.lsp.test;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * Combined suite for fast test classes (each under ~5s).
 * Running them together avoids 3× JVM startup overhead.
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    FoldingRangeTest.class,
    LspProtocolTest.class,
    SemanticTokensTest.class,
})
public class FastTests {}
