package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Smoke tests for the legacy temp-file disk I/O path in
 * {@link CheckRunner#runCheckDirWithContext}.
 *
 * <p>Sets {@link CheckRunner#useMockFiles} to {@code false} before each test
 * and restores it to {@code true} in {@code @After}, so the legacy code path
 * is exercised without permanently affecting other tests that rely on the
 * default mock-file behaviour.
 *
 * <p>These tests cover the same basic scenarios as {@link CheckRunnerDirTest}
 * to confirm that removing the legacy code path would break them, and to act
 * as a safety net if the mock-file path is ever disabled for debugging.
 */
public class LegacyDiskIOSmokeTest extends LspTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    @Before
    public void disableMockFiles() {
        CheckRunner.useMockFiles = false;
    }

    @After
    public void restoreMockFiles() {
        CheckRunner.useMockFiles = true;
    }

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
    // runCheckDir: basic type error (no snapshot)
    // -----------------------------------------------------------------------

    /**
     * A file with a type error must produce diagnostics via the legacy path
     * (no snapshot, direct disk read).
     */
    @Test
    public void testTypeError_Legacy() throws IOException {
        File f = writeJava("LegacyTypeErr.java",
                "public class LegacyTypeErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        CheckRunner.DirCheckResult result =
                CheckRunner.runCheckDir(List.of(f.getAbsolutePath()), new OpenJMLSettings());

        boolean hasError = result.diagnosticsByUri().values().stream()
                .anyMatch(d -> !d.isEmpty());
        assertTrue("Legacy path: expected diagnostics for type-error file", hasError);
    }

    // -----------------------------------------------------------------------
    // runCheckDir: clean file produces no diagnostics
    // -----------------------------------------------------------------------

    /**
     * A clean file must produce no diagnostics via the legacy path.
     */
    @Test
    public void testCleanFile_Legacy() throws IOException {
        File f = writeJava("LegacyClean.java",
                "public class LegacyClean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");

        CheckRunner.DirCheckResult result =
                CheckRunner.runCheckDir(List.of(f.getAbsolutePath()), new OpenJMLSettings());

        assertEquals("Legacy path: expected exit code 0 for clean file", 0, result.exitCode());
        for (List<Diagnostic> diags : result.diagnosticsByUri().values()) {
            assertTrue("Legacy path: expected no diagnostics for clean file", diags.isEmpty());
        }
    }

    // -----------------------------------------------------------------------
    // runCheckDirWithContext: dirty snapshot substitutes clean disk
    // -----------------------------------------------------------------------

    /**
     * When a dirty snapshot overrides a clean disk file, the legacy temp-file
     * path must compile the snapshot content and return the resulting diagnostics.
     */
    @Test
    public void testDirtySubstitutesCleanDisk_Legacy() throws IOException {
        // Disk file is clean.
        File f = writeJava("LegacyDirty.java",
                "public class LegacyDirty {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");

        // Snapshot carries a version with a type error.
        String dirtyContent =
                "public class LegacyDirty {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";

        CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(
                List.of(f.getAbsolutePath()),
                Map.of(fileUri(f), dirtyContent),
                new OpenJMLSettings());

        boolean hasError = result.diagnosticsByUri().values().stream()
                .anyMatch(d -> !d.isEmpty());
        assertTrue("Legacy path: expected error from dirty snapshot content", hasError);
    }

    // -----------------------------------------------------------------------
    // runCheckDirWithContext: empty snapshot fast path
    // -----------------------------------------------------------------------

    /**
     * When the snapshot is empty the legacy path delegates to
     * {@link CheckRunner#runCheckDir} (fast path) and must still catch
     * errors on disk.
     */
    @Test
    public void testEmptySnapshotFastPath_Legacy() throws IOException {
        File f = writeJava("LegacyEmpty.java",
                "public class LegacyEmpty {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(
                List.of(f.getAbsolutePath()), Map.of(), new OpenJMLSettings());

        boolean hasError = result.diagnosticsByUri().values().stream()
                .anyMatch(d -> !d.isEmpty());
        assertTrue("Legacy path: expected diagnostics via empty-snapshot fast path", hasError);
    }

    // -----------------------------------------------------------------------
    // Diagnostic keys: no temp-path leaks
    // -----------------------------------------------------------------------

    /**
     * Diagnostic keys returned by the legacy path must be real {@code file://}
     * URIs, not the internal temp-file paths used during compilation.
     */
    @Test
    public void testDiagnosticKeysAreRealUris_Legacy() throws IOException {
        File f = writeJava("LegacyUriCheck.java",
                "public class LegacyUriCheck {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        String dirtyContent =
                "public class LegacyUriCheck {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";

        CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(
                List.of(f.getAbsolutePath()),
                Map.of(fileUri(f), dirtyContent),
                new OpenJMLSettings());

        for (String key : result.diagnosticsByUri().keySet()) {
            assertFalse("Legacy path: diagnostic key must not be a temp-dir path: " + key,
                    key.contains("openjml-lsp-check-"));
            assertTrue("Legacy path: diagnostic key must be a file:// URI: " + key,
                    key.startsWith("file:"));
        }
    }
}
