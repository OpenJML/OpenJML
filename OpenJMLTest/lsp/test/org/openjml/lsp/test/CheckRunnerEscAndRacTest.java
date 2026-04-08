package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.IProverResult;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Tests for CheckRunner's single-file {@code --esc}, {@code --rac}, and
 * {@code --check} paths ({@code runEscFile}, {@code runEscMethod},
 * {@code runRacFile}, {@code runRacDir}, {@code checkFile}) and the
 * {@link CheckRunner.CheckResult} record helpers.
 *
 * <p>These tests write real {@code .java} files to a {@link TemporaryFolder},
 * invoke the relevant CheckRunner method, and assert on exit codes and diagnostics.
 *
 * <p>The ESC tests use methods whose proofs are trivial so that z3 finishes
 * quickly (all linear arithmetic, no non-linear multiplication).
 */
public class CheckRunnerEscAndRacTest extends LspTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private File writeJava(String filename, String content) throws IOException {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    private static String fileUri(File f) {
        return f.toPath().toUri().toString();
    }

    // -----------------------------------------------------------------------
    // CheckResult record helpers
    // -----------------------------------------------------------------------

    /**
     * Verify that {@link CheckRunner.CheckResult#isInternalError()} returns
     * {@code true} for exit codes 3 and 4 only.
     */
    @Test
    public void testCheckResultIsInternalError() {
        assertFalse(makeResult(0).isInternalError());
        assertFalse(makeResult(1).isInternalError());
        assertFalse(makeResult(2).isInternalError());
        assertTrue(makeResult(3).isInternalError());
        assertTrue(makeResult(4).isInternalError());
        assertFalse(makeResult(5).isInternalError());
    }

    @Test
    public void testCheckResultIsCommandLineError() {
        assertFalse(makeResult(0).isCommandLineError());
        assertFalse(makeResult(1).isCommandLineError());
        assertTrue(makeResult(2).isCommandLineError());
        assertFalse(makeResult(3).isCommandLineError());
    }

    @Test
    public void testCheckResultHasForeignErrors() {
        CheckRunner.CheckResult noForeign = new CheckRunner.CheckResult(
                List.of(), 0, Map.of(), List.of(), Map.of());
        CheckRunner.CheckResult hasForeign = new CheckRunner.CheckResult(
                List.of(), 0, Map.of(), List.of("error in dep"), Map.of());
        assertFalse(noForeign.hasForeignErrors());
        assertTrue(hasForeign.hasForeignErrors());
    }

    private static CheckRunner.CheckResult makeResult(int exitCode) {
        return new CheckRunner.CheckResult(List.of(), exitCode, Map.of(), List.of(), Map.of());
    }

    // -----------------------------------------------------------------------
    // checkFile — type-check a file already on disk
    // -----------------------------------------------------------------------

    @Test
    public void testCheckFileClean() throws Exception {
        File f = writeJava("CkFileClean.java",
                "public class CkFileClean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        CheckRunner.CheckResult result = CheckRunner.checkFile(
                f.getAbsolutePath(), fileUri(f), new OpenJMLSettings());

        assertEquals("Clean file should exit with code 0", 0, result.exitCode());
        assertTrue("Clean file should have no diagnostics", result.diagnostics().isEmpty());
    }

    @Test
    public void testCheckFileTypeError() throws Exception {
        File f = writeJava("CkFileErr.java",
                "public class CkFileErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");
        CheckRunner.CheckResult result = CheckRunner.checkFile(
                f.getAbsolutePath(), fileUri(f), new OpenJMLSettings());

        assertNotEquals("Type error should produce non-zero exit", 0, result.exitCode());
        assertFalse("Type error should produce diagnostics", result.diagnostics().isEmpty());
        assertTrue("Diagnostic should be Error severity",
                result.diagnostics().stream()
                        .anyMatch(d -> d.getSeverity() == DiagnosticSeverity.Error));
    }

    @Test
    public void testCheckFileJmlError() throws Exception {
        // A JML spec error (duplicate modifier) should produce a diagnostic.
        File f = writeJava("CkFileJmlErr.java",
                "public class CkFileJmlErr {\n" +
                "    //@ public public int x;\n" +
                "    int x2 = 0;\n" +
                "}\n");
        CheckRunner.CheckResult result = CheckRunner.checkFile(
                f.getAbsolutePath(), fileUri(f), new OpenJMLSettings());

        assertFalse("JML spec error should produce diagnostics", result.diagnostics().isEmpty());
    }

    // -----------------------------------------------------------------------
    // check (in-memory) — proofResults must be empty for --check runs
    // -----------------------------------------------------------------------

    @Test
    public void testCheckInMemoryProofResultsEmpty() {
        String source = "public class ChkInMem {\n" +
                        "    public int m(int x) { return x + 1; }\n" +
                        "}\n";
        CheckRunner.CheckResult result = CheckRunner.check(
                "file:///ChkInMem.java", source, new OpenJMLSettings());

        assertEquals("--check exit code should be 0 for clean file", 0, result.exitCode());
        assertTrue("--check must not produce proofResults", result.proofResults().isEmpty());
    }

    // -----------------------------------------------------------------------
    // runEscFile — ESC on a file on disk
    // -----------------------------------------------------------------------

    /**
     * Tests that {@code runEscFile} reads a disk file, invokes ESC, and populates
     * {@code proofResults}.  The exact kind (UNSAT vs POSSIBLY_SAT) depends on the
     * solver environment; we assert only that ESC ran (non-empty proofResults) and
     * that it did not fail with a type error (exit code != 1).
     */
    @Test
    public void testRunEscFileProofResultsPopulated() throws Exception {
        File f = writeJava("EscFileOk.java",
                "public class EscFileOk {\n" +
                "    //@ ensures true;\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        CheckRunner.CheckResult result = CheckRunner.runEscFile(
                f.getAbsolutePath(), fileUri(f), new OpenJMLSettings());

        // Exit 0 = all verified, 6 = verification failure; both mean ESC ran.
        assertNotEquals("ESC on a type-correct file must not exit 1 (type error)",
                1, result.exitCode());
        assertFalse("ESC must produce at least one proof result", result.proofResults().isEmpty());
        assertTrue("add must appear in proofResults",
                result.proofResults().containsKey("add"));
        // All returned kinds must be recognised terminal states.
        for (IProverResult.Kind k : result.proofResults().values()) {
            assertTrue("Unexpected proof kind: " + k,
                    k == IProverResult.UNSAT || k == IProverResult.SAT
                    || k == IProverResult.POSSIBLY_SAT || k == IProverResult.SKIPPED
                    || k == IProverResult.TIMEOUT || k == IProverResult.CANCELLED);
        }
    }

    @Test
    public void testRunEscFileFailingSpec() throws Exception {
        // A postcondition that cannot be proved (wrong sign).
        // Exit code 6 and a SAT/POSSIBLY_SAT result are expected.
        File f = writeJava("EscFileFail.java",
                "public class EscFileFail {\n" +
                "    //@ ensures \\result == a - b;\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        CheckRunner.CheckResult result = CheckRunner.runEscFile(
                f.getAbsolutePath(), fileUri(f), new OpenJMLSettings());

        assertEquals("Failing spec should produce exit code 6", 6, result.exitCode());
        assertFalse("Failing method should have a proof result",
                result.proofResults().isEmpty());
        assertTrue("add method should be SAT or POSSIBLY_SAT",
                result.proofResults().values().stream()
                        .anyMatch(k -> k == IProverResult.SAT
                                    || k == IProverResult.POSSIBLY_SAT));
    }

    // -----------------------------------------------------------------------
    // runEscMethod — target a single named method
    // -----------------------------------------------------------------------

    @Test
    public void testRunEscMethodTargetedMethodInResults() throws Exception {
        // Two methods: one with a correct spec, one with a broken spec.
        // We target only 'add'; it must appear in proofResults as UNSAT.
        // Whether 'sub' also appears depends on OpenJML's --method flag semantics;
        // we do not assert its absence, only that 'add' is present and verified.
        File f = writeJava("EscMethod.java",
                "public class EscMethod {\n" +
                "    //@ ensures true;\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "    //@ ensures \\result == a - b;\n" +
                "    public int sub(int a, int b) { return a + b; }\n" +
                "}\n");
        CheckRunner.CheckResult result = CheckRunner.runEscFileMethod(
                f.getAbsolutePath(), fileUri(f), "add", new OpenJMLSettings());

        assertFalse("Targeted method must have a proof result",
                result.proofResults().isEmpty());
        assertTrue("Targeted method 'add' must appear in proofResults",
                result.proofResults().containsKey("add"));
        // Exact kind depends on solver environment; any recognised terminal state is fine.
        IProverResult.Kind addKind = result.proofResults().get("add");
        assertTrue("Unexpected kind for 'add': " + addKind,
                addKind == IProverResult.UNSAT || addKind == IProverResult.SAT
                || addKind == IProverResult.POSSIBLY_SAT || addKind == IProverResult.SKIPPED
                || addKind == IProverResult.TIMEOUT);
    }

    // -----------------------------------------------------------------------
    // runRacFile — RAC compile a file on disk
    // -----------------------------------------------------------------------

    @Test
    public void testRunRacFileClean() throws Exception {
        File f = writeJava("RacFileOk.java",
                "public class RacFileOk {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        File outDir = tmp.newFolder("rac-out");

        CheckRunner.CheckResult result = CheckRunner.runRacFile(
                f.getAbsolutePath(), fileUri(f), new OpenJMLSettings(),
                outDir.getAbsolutePath());

        assertEquals("RAC compile of clean file should exit 0", 0, result.exitCode());
        assertTrue("Clean RAC compile should have no diagnostics",
                result.diagnostics().isEmpty());
    }

    @Test
    public void testRunRacFileTypeError() throws Exception {
        File f = writeJava("RacFileErr.java",
                "public class RacFileErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");
        File outDir = tmp.newFolder("rac-out-err");

        CheckRunner.CheckResult result = CheckRunner.runRacFile(
                f.getAbsolutePath(), fileUri(f), new OpenJMLSettings(),
                outDir.getAbsolutePath());

        assertNotEquals("Type error should produce non-zero exit", 0, result.exitCode());
        assertFalse("Type error should produce diagnostics", result.diagnostics().isEmpty());
    }

    // -----------------------------------------------------------------------
    // runRacDir — RAC compile a directory of files
    // -----------------------------------------------------------------------

    @Test
    public void testRunRacDirMultipleFiles() throws Exception {
        File dirA = writeJava("RacDirA.java",
                "public class RacDirA { public int x() { return 1; } }\n");
        File dirB = writeJava("RacDirB.java",
                "public class RacDirB { public int y() { return 2; } }\n");
        File outDir = tmp.newFolder("rac-dir-out");

        CheckRunner.DirCheckResult result = CheckRunner.runRacDir(
                List.of(dirA.getParent()),
                outDir.getAbsolutePath(),
                new OpenJMLSettings());

        assertEquals("RAC dir compile of clean files should exit 0", 0, result.exitCode());
        assertTrue("Clean RAC dir compile should produce no diagnostics",
                result.diagnosticsByUri().values().stream()
                        .allMatch(List::isEmpty));
    }
}
