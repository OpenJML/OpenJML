package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.Assert.*;

/**
 * Tests for {@link CheckRunner#runCheckDir} and {@link CheckRunner#runRacPaths},
 * which are the new path-list dispatch methods used by the unified
 * {@code openjml.checkJML} and {@code openjml.runRac} command handlers.
 *
 * <p>Each test writes one or more real {@code .java} files to a
 * {@link TemporaryFolder}, then invokes the relevant {@code CheckRunner}
 * method with the file's OS path.
 */
public class CheckRunnerDirTest extends LspTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Write {@code content} to a new file named {@code filename} in the temp folder. */
    private File writeJava(String filename, String content) throws IOException {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) {
            w.write(content);
        }
        return f;
    }

    /**
     * Return the {@code file:///} URI for {@code f}.
     *
     * <p>Uses {@code f.toPath().toUri()} rather than {@code f.toURI()} because
     * the latter produces a single-slash form ({@code file:/path}) while
     * {@link java.nio.file.Path#toUri()} produces the three-slash form
     * ({@code file:///path}) that the LSP server uses internally.  The two
     * string representations are logically equivalent but fail {@code equals}
     * comparison, which would break the snapshot-key lookup in
     * {@link CheckRunner#runCheckDirWithContext}.
     */
    private static String fileUri(File f) {
        return f.toPath().toUri().toString();
    }

    // -----------------------------------------------------------------------
    // runCheckDir — single file with type error
    // -----------------------------------------------------------------------

    /**
     * A single file with a type error passed to {@link CheckRunner#runCheckDir}
     * must produce Error-severity diagnostics keyed to that file's URI.
     */
    @Test
    public void testRunCheckDirTypeError() throws Exception {
        File f = writeJava("CkDirTypeErr.java",
                "public class CkDirTypeErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        CheckRunner.DirCheckResult result =
                CheckRunner.runCheckDir(List.of(f.getAbsolutePath()), new OpenJMLSettings());

        Map<String, List<Diagnostic>> byFile = result.diagnosticsByUri();
        assertFalse("Expected non-empty diagnostics map", byFile.isEmpty());

        // Diagnostics may be keyed by the canonical URI or by the path; find the entry.
        List<Diagnostic> diags = null;
        for (Map.Entry<String, List<Diagnostic>> e : byFile.entrySet()) {
            if (e.getKey().contains("CkDirTypeErr")) {
                diags = e.getValue();
                break;
            }
        }
        assertNotNull("Expected diagnostics for CkDirTypeErr.java", diags);
        assertFalse("Expected at least one diagnostic for type error", diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // runCheckDir — clean file produces no diagnostics
    // -----------------------------------------------------------------------

    /**
     * A single clean file passed to {@link CheckRunner#runCheckDir}
     * must produce an empty (or absent) diagnostics entry and exit code 0.
     */
    @Test
    public void testRunCheckDirClean() throws Exception {
        File f = writeJava("CkDirClean.java",
                "public class CkDirClean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");

        CheckRunner.DirCheckResult result =
                CheckRunner.runCheckDir(List.of(f.getAbsolutePath()), new OpenJMLSettings());

        assertEquals("Expected exit code 0 for clean file", 0, result.exitCode());
        for (List<Diagnostic> diags : result.diagnosticsByUri().values()) {
            assertTrue("Expected no diagnostics in any file for clean source", diags.isEmpty());
        }
    }

    // -----------------------------------------------------------------------
    // runCheckDir — multiple paths, mixed clean/error
    // -----------------------------------------------------------------------

    /**
     * Two files passed together: one clean, one with a type error.
     * Diagnostics must appear only for the erroneous file.
     */
    @Test
    public void testRunCheckDirMultiplePaths() throws Exception {
        File good = writeJava("CkDirGood.java",
                "public class CkDirGood {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        File bad = writeJava("CkDirBad.java",
                "public class CkDirBad {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        CheckRunner.DirCheckResult result = CheckRunner.runCheckDir(
                List.of(good.getAbsolutePath(), bad.getAbsolutePath()),
                new OpenJMLSettings());

        // Find diagnostics for the erroneous file.
        List<Diagnostic> badDiags = null;
        List<Diagnostic> goodDiags = null;
        for (Map.Entry<String, List<Diagnostic>> e : result.diagnosticsByUri().entrySet()) {
            if (e.getKey().contains("CkDirBad"))  badDiags  = e.getValue();
            if (e.getKey().contains("CkDirGood")) goodDiags = e.getValue();
        }

        assertNotNull("Expected diagnostics entry for CkDirBad.java", badDiags);
        assertFalse("Expected at least one diagnostic for CkDirBad.java", badDiags.isEmpty());

        if (goodDiags != null) {
            assertTrue("Expected no diagnostics for CkDirGood.java", goodDiags.isEmpty());
        }
    }

    // -----------------------------------------------------------------------
    // runCheckDir — settings override (propertiesFile)
    // -----------------------------------------------------------------------

    /**
     * Passes a generated properties file that sets {@code require-white-space=true},
     * which causes JML comments without a space after {@code @} (e.g. {@code //@ensures})
     * to be treated as ordinary Java comments.  A JML expression that would
     * be a name-resolution error under normal parsing is silently ignored when
     * the flag is active — confirming that the properties file is honoured.
     *
     * <p>Source: {@code //@requires unknownIdent > 0;} (no space after @).
     * Without the flag this is a JML parse error ({@code unknownIdent} is undefined).
     * With {@code require-white-space=true} the comment is not parsed as JML and
     * produces no diagnostic.
     */
    @Test
    public void testRunCheckDirWithPropertiesFileOverride() throws Exception {
        // A file whose JML annotation uses an undefined identifier — this is
        // an error when parsed as JML, but not when treated as a plain comment.
        File f = writeJava("CkDirPropsOverride.java",
                "public class CkDirPropsOverride {\n" +
                "    //@requires unknownIdentifier > 0;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n");

        // Without the override: JML is parsed and unknownIdentifier causes a diagnostic.
        CheckRunner.DirCheckResult defaultResult =
                CheckRunner.runCheckDir(List.of(f.getAbsolutePath()), new OpenJMLSettings());
        boolean hasDefaultDiag = defaultResult.diagnosticsByUri().values().stream()
                .anyMatch(d -> !d.isEmpty());
        assertTrue("Expected a JML error for unknownIdentifier without properties override",
                hasDefaultDiag);

        // With require-white-space=true: //@requires is a plain comment — no JML error.
        File props = tmp.newFile("override.properties");
        try (FileWriter w = new FileWriter(props)) {
            w.write("org.openjml.option.require-white-space=true\n");
        }
        OpenJMLSettings overrideSettings = new OpenJMLSettings();
        overrideSettings.generatedPropertiesFile = props.getAbsolutePath();

        CheckRunner.DirCheckResult overrideResult =
                CheckRunner.runCheckDir(List.of(f.getAbsolutePath()), overrideSettings);
        boolean hasOverrideDiag = overrideResult.diagnosticsByUri().values().stream()
                .anyMatch(d -> !d.isEmpty());
        assertFalse("Expected no JML diagnostics when require-white-space=true suppresses JML parsing",
                hasOverrideDiag);
    }

    // -----------------------------------------------------------------------
    // runCheckDirWithContext — dirty snapshot substitutes disk content
    // -----------------------------------------------------------------------

    /**
     * When a file on disk is clean but the snapshot carries error-content for
     * the same URI, {@link CheckRunner#runCheckDirWithContext} must produce
     * diagnostics from the snapshot rather than the clean on-disk version.
     *
     * <p>This is the core behaviour added by the dirty-file snapshot policy:
     * a path-based check (toolbar button) sees unsaved editor edits.
     */
    @Test
    public void testRunCheckDirWithContext_DirtySubstitutesCleanDisk() throws Exception {
        // Disk file is clean — no errors.
        File f = writeJava("CkCtxDirty.java",
                "public class CkCtxDirty {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");

        // Confirm disk produces no diagnostics without the snapshot.
        CheckRunner.DirCheckResult diskResult =
                CheckRunner.runCheckDir(List.of(f.getAbsolutePath()), new OpenJMLSettings());
        boolean diskHasError = diskResult.diagnosticsByUri().values().stream()
                .anyMatch(d -> !d.isEmpty());
        assertFalse("Baseline: clean disk file should produce no diagnostics", diskHasError);

        // Snapshot carries a version of the file that has a type error.
        String dirtyContent =
                "public class CkCtxDirty {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";
        Map<String, String> snapshot = Map.of(fileUri(f), dirtyContent);

        CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(
                List.of(f.getAbsolutePath()), snapshot, new OpenJMLSettings());

        // Find the diagnostics for our file.
        List<Diagnostic> diags = null;
        for (Map.Entry<String, List<Diagnostic>> e : result.diagnosticsByUri().entrySet()) {
            if (e.getKey().contains("CkCtxDirty")) {
                diags = e.getValue();
                break;
            }
        }
        assertNotNull("Expected diagnostics entry for CkCtxDirty.java", diags);
        assertFalse("Expected error diagnostic from dirty snapshot content", diags.isEmpty());
    }

    /**
     * When the snapshot is empty, {@link CheckRunner#runCheckDirWithContext}
     * takes the fast path and delegates to {@link CheckRunner#runCheckDir}.
     * A file with a type error on disk must still produce diagnostics.
     */
    @Test
    public void testRunCheckDirWithContext_EmptySnapshotFastPath() throws Exception {
        File f = writeJava("CkCtxEmpty.java",
                "public class CkCtxEmpty {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(
                List.of(f.getAbsolutePath()), Map.of(), new OpenJMLSettings());

        boolean hasError = result.diagnosticsByUri().values().stream()
                .anyMatch(d -> !d.isEmpty());
        assertTrue("Expected diagnostics for disk-file error with empty snapshot (fast path)",
                hasError);
    }

    /**
     * When a dirty snapshot has content for a file in the path list AND clean content
     * for that file on disk, the dirty version wins and is checked.
     * When a second file in the same directory has errors on disk AND is not in the
     * snapshot, the disk version is used and its errors are reported.
     *
     * <p>This verifies that the context mechanism only substitutes files that appear
     * in the snapshot, leaving unmodified files unchanged.
     */
    @Test
    public void testRunCheckDirWithContext_OnlyDirtyFilesSubstituted() throws Exception {
        // File A: clean on disk; dirty snapshot introduces an error.
        File fileA = writeJava("CkCtxA.java",
                "public class CkCtxA {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");

        // File B: error on disk; not in the snapshot.
        File fileB = writeJava("CkCtxB.java",
                "public class CkCtxB {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        String dirtyA =
                "public class CkCtxA {\n" +
                "    public int bad() { return \"wrong\"; }\n" +
                "}\n";
        Map<String, String> snapshot = Map.of(fileUri(fileA), dirtyA);

        CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(
                List.of(fileA.getAbsolutePath(), fileB.getAbsolutePath()),
                snapshot, new OpenJMLSettings());

        boolean aHasError = false, bHasError = false;
        for (Map.Entry<String, List<Diagnostic>> e : result.diagnosticsByUri().entrySet()) {
            if (e.getKey().contains("CkCtxA") && !e.getValue().isEmpty()) aHasError = true;
            if (e.getKey().contains("CkCtxB") && !e.getValue().isEmpty()) bHasError = true;
        }
        assertTrue("Expected error in file A from dirty snapshot", aHasError);
        assertTrue("Expected error in file B from disk (not in snapshot)", bHasError);
    }

    // -----------------------------------------------------------------------
    // runRacPaths — clean file produces class file
    // -----------------------------------------------------------------------

    /**
     * A single clean file passed to {@link CheckRunner#runRacPaths} must compile
     * successfully (exit code 0) and produce a {@code .class} file in the output
     * directory.
     */
    @Test
    public void testRunRacPathsProducesClassFile() throws Exception {
        File f = writeJava("RacPathsClean.java",
                "public class RacPathsClean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");

        Path outDir = tmp.newFolder("rac-out").toPath();
        OpenJMLSettings settings = new OpenJMLSettings();
        settings.racOutputDir = outDir.toString();

        CheckRunner.CheckResult result =
                CheckRunner.runRacPaths(List.of(f.getAbsolutePath()), settings);

        assertEquals("Expected exit code 0 for clean RAC compilation", 0, result.exitCode());

        // The RAC-compiled class file must appear in the output directory.
        Path classFile = outDir.resolve("RacPathsClean.class");
        assertTrue("Expected RacPathsClean.class in RAC output directory",
                Files.exists(classFile));
    }

    // -----------------------------------------------------------------------
    // runRacPaths — type error yields non-zero exit
    // -----------------------------------------------------------------------

    /**
     * A file with a type error passed to {@link CheckRunner#runRacPaths} must
     * return a non-zero exit code, and no class file must be produced for the
     * erroneous class.
     */
    // -----------------------------------------------------------------------
    // runEscDir — with per-file callback
    // -----------------------------------------------------------------------

    /**
     * {@link CheckRunner#runEscDir(List, OpenJMLSettings, java.util.function.BiConsumer)}
     * must invoke the callback at least once per verified method, and the URI
     * argument must be a {@code file://} URI (not a bare path).
     */
    @Test
    public void testRunEscDirWithCallback() throws Exception {
        File f = writeJava("EscDirCb.java",
                "public class EscDirCb {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n");

        List<String> callbackUris = new ArrayList<>();
        AtomicInteger callbackCount = new AtomicInteger(0);

        CheckRunner.runEscDir(
                List.of(f.getAbsolutePath()),
                new OpenJMLSettings(),
                (uri, diags) -> {
                    callbackUris.add(uri);
                    callbackCount.incrementAndGet();
                });

        assertTrue("Expected runEscDir callback to be called at least once",
                callbackCount.get() > 0);
        for (String uri : callbackUris) {
            assertTrue("Callback URI must be a file:// URI: " + uri,
                    uri.startsWith("file:"));
        }
    }

    // -----------------------------------------------------------------------
    // runRacPaths — type error yields non-zero exit
    // -----------------------------------------------------------------------

    /**
     * A file with a type error passed to {@link CheckRunner#runRacPaths} must
     * return a non-zero exit code, and no class file must be produced for the
     * erroneous class.
     */
    @Test
    public void testRunRacPathsTypeErrorExitCode() throws Exception {
        File f = writeJava("RacPathsErr.java",
                "public class RacPathsErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        Path outDir = tmp.newFolder("rac-out-err").toPath();
        OpenJMLSettings settings = new OpenJMLSettings();
        settings.racOutputDir = outDir.toString();

        CheckRunner.CheckResult result =
                CheckRunner.runRacPaths(List.of(f.getAbsolutePath()), settings);

        assertNotEquals("Expected non-zero exit code for RAC compile with type error",
                0, result.exitCode());

        Path classFile = outDir.resolve("RacPathsErr.class");
        assertFalse("Expected no class file when RAC compilation fails",
                Files.exists(classFile));
    }
}
