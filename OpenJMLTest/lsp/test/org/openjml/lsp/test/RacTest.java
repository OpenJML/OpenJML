package org.openjml.lsp.test;

import org.eclipse.lsp4j.DiagnosticSeverity;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.List;

import static org.junit.Assert.*;

/**
 * Unit tests for the RAC (Runtime Assertion Checking) compilation helpers in
 * {@link CheckRunner}: {@link CheckRunner#runRacFile} and {@link CheckRunner#runRacDir}.
 *
 * <p>These tests call {@code CheckRunner} directly (not via LSP protocol).
 * End-to-end RAC via the LSP {@code openjml.runRac} command is covered by
 * {@link CommandDispatchTest}.
 *
 * <p>RAC requires on-disk Java source files (unlike {@code --check} / {@code --esc}
 * which accept in-memory content).  Each test writes temporary source files,
 * runs the RAC compilation into a temporary output directory, and asserts on
 * the resulting diagnostics and exit code.
 */
public class RacTest {

    private Path tempDir;

    @Before
    public void setUp() throws IOException {
        tempDir = Files.createTempDirectory("openjml-rac-test-");
    }

    @After
    public void tearDown() throws IOException {
        if (tempDir != null && Files.exists(tempDir)) {
            Files.walk(tempDir)
                    .sorted(Comparator.reverseOrder())
                    .forEach(p -> { try { Files.delete(p); } catch (IOException ignored) {} });
        }
    }

    // -----------------------------------------------------------------------
    // runRacFile
    // -----------------------------------------------------------------------

    /**
     * A syntactically and semantically valid Java file should RAC-compile with
     * exit code 0 and produce no diagnostic errors.
     */
    @Test
    public void testRunRacFileCleanProducesNoDiagnostics() throws Exception {
        Path src = writeSource("RacClean.java",
                "public class RacClean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        Path outDir = Files.createDirectories(tempDir.resolve("out"));

        CheckRunner.CheckResult result = CheckRunner.runRacFile(
                src.toString(), src.toUri().toString(), new OpenJMLSettings(),
                outDir.toString());

        assertEquals("RAC should exit 0 for valid Java", 0, result.exitCode());
        assertTrue("Expected no diagnostics for valid Java", result.diagnostics().isEmpty());
    }

    /**
     * A Java source file with a type error must produce at least one
     * Error-severity diagnostic and a non-zero exit code from RAC compilation.
     */
    @Test
    public void testRunRacFileTypeErrorProducesDiagnostic() throws Exception {
        Path src = writeSource("RacTypeErr.java",
                "public class RacTypeErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");
        Path outDir = Files.createDirectories(tempDir.resolve("out"));

        CheckRunner.CheckResult result = CheckRunner.runRacFile(
                src.toString(), src.toUri().toString(), new OpenJMLSettings(),
                outDir.toString());

        assertNotEquals("RAC should exit non-zero for type error", 0, result.exitCode());
        assertFalse("Expected at least one diagnostic for type error",
                result.diagnostics().isEmpty());
        assertTrue("Expected Error-severity diagnostic",
                result.diagnostics().stream()
                        .anyMatch(d -> d.getSeverity() == DiagnosticSeverity.Error));
    }

    // -----------------------------------------------------------------------
    // runRacDir
    // -----------------------------------------------------------------------

    /**
     * {@code runRacDir} on a single valid Java file should exit 0 and produce
     * no diagnostics.
     *
     * <p>This also exercises the output-directory resolution logic: the caller
     * supplies an absolute path so the server uses it directly without resolving
     * it relative to the workspace root.
     */
    @Test
    public void testRunRacDirCleanProducesNoDiagnostics() throws Exception {
        Path src = writeSource("RacDirClean.java",
                "public class RacDirClean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        Path outDir = Files.createDirectories(tempDir.resolve("out"));

        CheckRunner.DirCheckResult result = CheckRunner.runRacDir(
                List.of(src.toString()), outDir.toString(), new OpenJMLSettings());

        assertEquals("runRacDir should exit 0 for valid Java", 0, result.exitCode());
        long errorCount = result.diagnosticsByUri().values().stream()
                .flatMap(List::stream)
                .filter(d -> d.getSeverity() == DiagnosticSeverity.Error)
                .count();
        assertEquals("Expected no Error diagnostics for valid Java", 0, errorCount);
    }

    /**
     * {@code runRacDir} on a file with a type error must produce Error-severity
     * diagnostics and a non-zero exit code.
     */
    @Test
    public void testRunRacDirTypeErrorProducesDiagnostic() throws Exception {
        Path src = writeSource("RacDirTypeErr.java",
                "public class RacDirTypeErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");
        Path outDir = Files.createDirectories(tempDir.resolve("out"));

        CheckRunner.DirCheckResult result = CheckRunner.runRacDir(
                List.of(src.toString()), outDir.toString(), new OpenJMLSettings());

        assertNotEquals("runRacDir should exit non-zero for type error", 0, result.exitCode());
        boolean anyErrors = result.diagnosticsByUri().values().stream()
                .flatMap(List::stream)
                .anyMatch(d -> d.getSeverity() == DiagnosticSeverity.Error);
        assertTrue("Expected at least one Error diagnostic from runRacDir", anyErrors);
    }

    /**
     * {@code runRacDir} with multiple source files should compile all of them
     * in a single pass.  With two valid files, both should compile cleanly.
     */
    @Test
    public void testRunRacDirMultipleCleanFiles() throws Exception {
        Path src1 = writeSource("RacMultiA.java",
                "public class RacMultiA {\n" +
                "    public int x() { return 1; }\n" +
                "}\n");
        Path src2 = writeSource("RacMultiB.java",
                "public class RacMultiB {\n" +
                "    public int y() { return 2; }\n" +
                "}\n");
        Path outDir = Files.createDirectories(tempDir.resolve("out"));

        CheckRunner.DirCheckResult result = CheckRunner.runRacDir(
                List.of(src1.toString(), src2.toString()), outDir.toString(),
                new OpenJMLSettings());

        assertEquals("runRacDir should exit 0 for two valid files", 0, result.exitCode());
        long errorCount = result.diagnosticsByUri().values().stream()
                .flatMap(List::stream)
                .filter(d -> d.getSeverity() == DiagnosticSeverity.Error)
                .count();
        assertEquals("Expected no Error diagnostics for two valid files", 0, errorCount);
    }

    // -----------------------------------------------------------------------
    // Helper
    // -----------------------------------------------------------------------

    private Path writeSource(String filename, String content) throws IOException {
        Path file = tempDir.resolve(filename);
        Files.writeString(file, content, StandardCharsets.UTF_8);
        return file;
    }
}
