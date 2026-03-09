package org.openjml.lsp.test;

import org.junit.Test;
import org.openjml.lsp.CheckRunner;

import java.util.Map;

import static org.junit.Assert.*;

/**
 * Multi-file ESC tests: verifies that type errors in a dependency prevent ESC
 * from running on the focus file, while errors in unrelated files are ignored.
 *
 * <p>File setup used by {@link #testEscCheckErrorFromDependency}:
 * <pre>
 *   A.java — focus file; has a failing postcondition; calls B.value()
 *   B.java — dependency of A; has a type error in its body
 *   C.java — unrelated to A; also has a type error; NOT passed to OpenJML
 * </pre>
 *
 * Expected behaviour: running ESC on A.java with B.java as context causes
 * exit code 1 (B's type error prevents compilation), no proof results are
 * recorded for A, and all of A's methods are reported as CHECK_ERROR.
 * C.java is excluded and its errors have no effect on the result.
 */
public class MultiFileEscTest extends LspTestBase {

    /**
     * A.java depends on B.java; B has a type error.
     * C.java also has a type error but is NOT a dependency of A and is NOT
     * passed to OpenJML.
     *
     * Expected:
     * <ul>
     *   <li>exit code 1 — B's type error prevents compilation</li>
     *   <li>proof results empty — ESC never ran</li>
     *   <li>diagnostics for A.java empty — B's error is in B.java and is
     *       filtered out by {@code DiagnosticConverter}; A itself is correct</li>
     * </ul>
     */
    @Test
    public void testEscCheckErrorFromDependency() throws Exception {
        // A.java: correct Java/JML; postcondition would fail ESC if it ran;
        // calls B.value() so it depends on B.java compiling successfully.
        String sourceA =
                "public class A {\n" +
                "    //@ ensures \\result > x;\n" +
                "    public int m(int x) { return new B().value(x); }\n" +
                "}\n";

        // B.java: type error — returns String where int is expected.
        // This prevents the entire compilation from succeeding.
        String sourceB =
                "public class B {\n" +
                "    public int value(int x) { return \"not an int\"; }\n" +
                "}\n";

        // C.java: also has a type error, but A does NOT depend on C.
        // C is deliberately excluded from the OpenJML invocation to confirm
        // that unrelated errors have no influence on the result.
        @SuppressWarnings("unused")
        String sourceC =
                "public class C {\n" +
                "    public int bad() { return \"not an int either\"; }\n" +
                "}\n";

        // Run ESC on A.java with B.java as context. C.java is NOT included.
        CheckRunner.CheckResult result = runEscWithSources(
                "file:///A.java", sourceA,
                Map.of("B.java", sourceB));

        // B's type error → compilation fails → exit code 1
        assertEquals("Expected exit code 1 (dependency B has a type error)", 1, result.exitCode());

        // ESC never ran — no proof results for A's methods
        assertTrue("Expected no proof results when a dependency has type errors",
                result.proofResults().isEmpty());

        // B's error is reported against B.java and filtered out of A's diagnostics.
        // A.java itself is well-typed, so no diagnostics should remain.
        assertTrue("Expected no diagnostics for A.java (B's error is in B.java, not A.java)",
                result.diagnostics().isEmpty());
    }
}
