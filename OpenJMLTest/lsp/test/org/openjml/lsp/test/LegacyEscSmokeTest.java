package org.openjml.lsp.test;

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
 * Smoke tests for the legacy temp-file disk I/O path in ESC-related methods of
 * {@link CheckRunner}.
 *
 * <p>Sets {@link CheckRunner#useMockFiles} to {@code false} before each test and
 * restores it in {@code @After}, so the legacy code paths are exercised without
 * permanently affecting other tests.
 *
 * <p>Covers:
 * <ul>
 *   <li>{@code runOnContentWithContext} ({@code --esc} branch) — reached via
 *       {@link CheckRunner#runEsc}</li>
 *   <li>{@code runEscWithSources} (legacy temp-dir path)</li>
 *   <li>{@code runEscDirWithContext} (legacy temp-dir path)</li>
 * </ul>
 */
public class LegacyEscSmokeTest extends LspTestBase {

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

    private File writeJava(String filename, String content) throws IOException {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    private static String fileUri(File f) {
        return f.toPath().toUri().toString();
    }

    // -----------------------------------------------------------------------
    // runEsc — runOnContentWithContext --esc legacy path
    // -----------------------------------------------------------------------

    /**
     * {@link CheckRunner#runEsc} with {@code useMockFiles=false} must write content
     * to a temp file, run {@code --esc} on it, and return a valid result.
     *
     * <p>This exercises the {@code else} branch of {@code runOnContentWithContext}
     * in {@code --esc} mode that creates {@code openjml-lsp-*} temp directories.
     * A trivially-true postcondition is used so the solver finishes quickly.
     */
    @Test
    public void testEscSingleFile_Legacy() {
        String source =
                "public class LegacyEscSingle {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int identity(int x) { return x; }\n" +
                "}\n";

        CheckRunner.CheckResult result = CheckRunner.runEsc(
                "file:///LegacyEscSingle.java", source);

        assertNotNull("Legacy ESC must return a result", result);
        assertTrue("Exit code must be non-negative (legacy ESC path completed)",
                result.exitCode() >= 0);
    }

    // -----------------------------------------------------------------------
    // runEscWithSources — legacy temp-dir path
    // -----------------------------------------------------------------------

    /**
     * {@link CheckRunner#runEscWithSources} with {@code useMockFiles=false} must
     * write the primary source to a temp directory and run {@code --esc} on it.
     *
     * <p>This exercises the {@code else} branch of {@code runEscWithSources} that
     * creates {@code openjml-lsp-*} temp directories, writes files via
     * {@code Files.writeString}, and passes their paths to {@code api.execute()}.
     */
    @Test
    public void testEscWithSources_Legacy() {
        String primaryUri = "file:///LegacyEscPrimary.java";
        String primaryContent =
                "public class LegacyEscPrimary {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int identity(int x) { return x; }\n" +
                "}\n";

        CheckRunner.CheckResult result = CheckRunner.runEscWithSources(
                primaryUri, primaryContent, Map.of());

        assertNotNull("Legacy runEscWithSources must return a result", result);
        assertTrue("Exit code must be non-negative", result.exitCode() >= 0);
    }

    // -----------------------------------------------------------------------
    // runEscDirWithContext — legacy temp-dir path
    // -----------------------------------------------------------------------

    /**
     * {@link CheckRunner#runEscDirWithContext} with {@code useMockFiles=false} and
     * a non-empty snapshot must use the legacy path: write snapshot files to a
     * temp directory and run {@code --esc} against that directory.
     *
     * <p>This exercises {@code runEscDirWithContextLegacy} which creates
     * {@code openjml-lsp-esc-*} temp directories and passes them to
     * {@code api.execute()}.
     */
    @Test
    public void testEscDirWithContext_Legacy() throws IOException {
        File f = writeJava("LegacyEscDir.java",
                "public class LegacyEscDir {\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n");

        // Snapshot carries trivially-verifiable specs over the clean disk file.
        String snapshotContent =
                "public class LegacyEscDir {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n";

        CheckRunner.DirCheckResult result = CheckRunner.runEscDirWithContext(
                List.of(f.getAbsolutePath()),
                Map.of(fileUri(f), snapshotContent),
                new OpenJMLSettings());

        assertNotNull("Legacy runEscDirWithContext must return a result", result);
        assertTrue("Exit code must be non-negative", result.exitCode() >= 0);
    }
}
