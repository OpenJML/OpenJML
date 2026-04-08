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
 * <h3>Arithmetic and overflow</h3>
 * <p>OpenJML adds implicit overflow proof obligations for integer arithmetic by
 * default.  A method body like {@code return a + b} will produce POSSIBLY_SAT
 * even with {@code ensures true} unless the ranges of {@code a} and {@code b}
 * are constrained by {@code requires} clauses or {@code code_java_math} is used.
 * ESC tests here use identity methods ({@code return x}) to avoid this.
 *
 * <h3>JML spec files ({@code .jml})</h3>
 * <p>If a {@code .jml} file with the same base name as the class is visible on
 * the specs path, OpenJML silently uses its method specs in place of the
 * {@code //@ ensures/requires} clauses written in the {@code .java} file (the
 * method body is unchanged).  Tests write to a temp folder with no matching
 * {@code .jml} files, so this does not affect the results here — but it is
 * worth knowing when debugging unexpected proof outcomes.
 * <p>Best practice: if a class has a companion {@code .jml} file, do not put
 * specs in the {@code .java} file at all, or add a comment such as
 * {@code // specs in Foo.jml} to make the split explicit.
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
     * Tests that {@code runEscFile} reads a disk file, invokes ESC, and verifies
     * the method as UNSAT (exit 0).
     *
     * <p>Uses an identity method ({@code return x}) rather than arithmetic to
     * avoid implicit integer-overflow proof obligations, which would produce
     * POSSIBLY_SAT without range preconditions.
     */
    @Test
    public void testRunEscFileVerified() throws Exception {
        File f = writeJava("EscFileOk.java",
                "public class EscFileOk {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int identity(int x) { return x; }\n" +
                "}\n");
        CheckRunner.CheckResult result = CheckRunner.runEscFile(
                f.getAbsolutePath(), fileUri(f), new OpenJMLSettings());

        assertEquals("Verified method should exit with code 0", 0, result.exitCode());
        assertTrue("identity must appear in proofResults",
                result.proofResults().containsKey("identity"));
        assertEquals("identity should be UNSAT (verified)",
                IProverResult.UNSAT, result.proofResults().get("identity"));
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

    /**
     * Targeting a single method via {@code runEscFileMethod} must produce a proof
     * result for that method.
     *
     * <p>Uses an identity method ({@code return x}) for the targeted method to
     * avoid overflow proof obligations that would prevent UNSAT without range
     * preconditions.
     */
    @Test
    public void testRunEscMethodTargetedMethodInResults() throws Exception {
        File f = writeJava("EscMethod.java",
                "public class EscMethod {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int identity(int x) { return x; }\n" +
                "    //@ ensures \\result == a - b;\n" +  // wrong — not targeted
                "    public int badSub(int a, int b) { return a + b; }\n" +
                "}\n");
        CheckRunner.CheckResult result = CheckRunner.runEscFileMethod(
                f.getAbsolutePath(), fileUri(f), "identity", new OpenJMLSettings());

        assertTrue("Targeted method 'identity' must appear in proofResults",
                result.proofResults().containsKey("identity"));
        assertEquals("Targeted method 'identity' should be UNSAT (verified)",
                IProverResult.UNSAT, result.proofResults().get("identity"));
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
