package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.CheckRunner;
import org.openjml.IProverResult;
import org.openjml.lsp.OpenJMLSettings;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.Assert.*;

/**
 * Tests for {@link CheckRunner#runEscDirWithContext} — the dirty-file snapshot
 * path used when toolbar/command ESC runs while files have unsaved edits.
 *
 * <p>Follows the same structure as {@link CheckRunnerDirTest}: real {@code .java}
 * files are written to a {@link TemporaryFolder} and checked via the static
 * {@code CheckRunner} methods.
 */
public class EscDirWithContextTest extends LspTestBase {

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

    /**
     * Three-slash {@code file:///} URI — must match the form {@link CheckRunner}
     * uses internally for snapshot key lookup.
     */
    private static String fileUri(File f) {
        return f.toPath().toUri().toString();
    }

    // -----------------------------------------------------------------------
    // Fast path: empty snapshot delegates to runEscDir
    // -----------------------------------------------------------------------

    /**
     * When the snapshot is empty, {@link CheckRunner#runEscDirWithContext}
     * takes the fast path and delegates to {@link CheckRunner#runEscDir}.
     * A file with a spec violation on disk must still produce an ESC diagnostic.
     */
    @Test
    public void testEmptySnapshotFastPath() throws Exception {
        File f = writeJava("EscCtxEmpty.java",
                "public class EscCtxEmpty {\n" +
                "    //@ ensures \\result > x;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n");

        CheckRunner.DirCheckResult result = CheckRunner.runEscDirWithContext(
                List.of(f.getAbsolutePath()), Map.of(), new OpenJMLSettings(), null);

        // ESC on this file must produce a proof result (POSSIBLY_FALSE — postcondition not met).
        // The key thing is the fast-path delegation ran and returned a populated result.
        assertNotNull("Expected non-null DirCheckResult for fast-path delegation", result);
        assertFalse("Expected at least one proof result from fast-path ESC run",
                result.proofResults().isEmpty());
    }

    // -----------------------------------------------------------------------
    // Dirty snapshot substitutes clean disk content
    // -----------------------------------------------------------------------

    /**
     * Disk file is clean (verifiable postcondition). Snapshot carries a version
     * with an unprovable postcondition. ESC must use the dirty snapshot content
     * and produce a proof failure, not verify the clean disk version.
     */
    @Test
    public void testDirtyFileSubstitutesClean() throws Exception {
        // Disk: trivially verifiable.
        File f = writeJava("EscCtxDirty.java",
                "public class EscCtxDirty {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n");

        // Snapshot: postcondition cannot be proved (body returns x+1).
        String dirtyContent =
                "public class EscCtxDirty {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int m(int x) { return x + 1; }\n" +
                "}\n";

        CheckRunner.DirCheckResult result = CheckRunner.runEscDirWithContext(
                List.of(f.getAbsolutePath()),
                Map.of(fileUri(f), dirtyContent),
                new OpenJMLSettings(), null);

        // The dirty content has a spec violation — expect at least one diagnostic or
        // a proof result that is not UNSAT.
        boolean hasDiag = result.diagnosticsByUri().values().stream().anyMatch(d -> !d.isEmpty());
        boolean hasFailure = result.proofResults().values().stream()
                .anyMatch(k -> k != IProverResult.UNSAT);
        assertTrue("Expected ESC failure from dirty snapshot (diagnostic or non-UNSAT proof)",
                hasDiag || hasFailure);
    }

    // -----------------------------------------------------------------------
    // Dirty snapshot overrides type error on disk
    // -----------------------------------------------------------------------

    /**
     * Disk file has a type error. Snapshot carries a corrected version.
     * {@link CheckRunner#runEscDirWithContext} must use the snapshot and
     * produce no type-error diagnostics.
     */
    @Test
    public void testDirtyFileOverridesTypeError() throws Exception {
        // Disk: type error (return type mismatch).
        File f = writeJava("EscCtxFixed.java",
                "public class EscCtxFixed {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        // Snapshot: corrected version with no type error.
        String fixedContent =
                "public class EscCtxFixed {\n" +
                "    //@ ensures \\result == 42;\n" +
                "    public int m() { return 42; }\n" +
                "}\n";

        CheckRunner.DirCheckResult result = CheckRunner.runEscDirWithContext(
                List.of(f.getAbsolutePath()),
                Map.of(fileUri(f), fixedContent),
                new OpenJMLSettings(), null);

        List<Diagnostic> diags = null;
        for (Map.Entry<String, List<Diagnostic>> e : result.diagnosticsByUri().entrySet()) {
            if (e.getKey().contains("EscCtxFixed")) { diags = e.getValue(); break; }
        }
        if (diags != null) {
            boolean hasTypeError = diags.stream().anyMatch(d -> {
                var msg = d.getMessage();
                return msg != null && msg.getLeft() != null
                        && msg.getLeft().contains("not an int");
            });
            assertFalse("Type error from disk must not appear when snapshot overrides it",
                    hasTypeError);
        }
        // No assert on exit code — ESC may still report a proof issue from the spec.
    }

    // -----------------------------------------------------------------------
    // Diagnostics map to real URIs, not temp paths
    // -----------------------------------------------------------------------

    /**
     * Diagnostics in the returned {@link CheckRunner.DirCheckResult} must be
     * keyed by the original real {@code file:///} URI, not by the
     * {@code /tmp/openjml-lsp-esc-*} temp-file path used during the run.
     */
    @Test
    public void testDiagnosticsMapToRealUri() throws Exception {
        File f = writeJava("EscCtxUri.java",
                "public class EscCtxUri {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n");

        // Dirty content with a type error to guarantee a non-empty diagnostic entry.
        String dirtyContent =
                "public class EscCtxUri {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";

        CheckRunner.DirCheckResult result = CheckRunner.runEscDirWithContext(
                List.of(f.getAbsolutePath()),
                Map.of(fileUri(f), dirtyContent),
                new OpenJMLSettings(), null);

        for (String key : result.diagnosticsByUri().keySet()) {
            assertFalse("Diagnostic key must not be a temp-dir path: " + key,
                    key.contains("openjml-lsp-esc-"));
            assertTrue("Diagnostic key must be a file:// URI: " + key,
                    key.startsWith("file:"));
        }
    }

    // -----------------------------------------------------------------------
    // Per-file callback receives real URI
    // -----------------------------------------------------------------------

    /**
     * When a non-null {@code perFileCallback} is supplied, it must be called
     * at least once per completed method, and the URI argument must be the
     * real {@code file:///} URI (not a temp path).
     */
    @Test
    public void testPerFileCallbackFired() throws Exception {
        File f = writeJava("EscCtxCb.java",
                "public class EscCtxCb {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n");

        String dirtyContent =
                "public class EscCtxCb {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n";

        List<String> callbackUris = new ArrayList<>();
        AtomicInteger callbackCount = new AtomicInteger(0);

        CheckRunner.runEscDirWithContext(
                List.of(f.getAbsolutePath()),
                Map.of(fileUri(f), dirtyContent),
                new OpenJMLSettings(),
                (uri, diags, partialResults) -> {
                    callbackUris.add(uri);
                    callbackCount.incrementAndGet();
                });

        assertTrue("Expected perFileCallback to be called at least once",
                callbackCount.get() > 0);
        for (String uri : callbackUris) {
            assertFalse("Callback URI must not be a temp path: " + uri,
                    uri.contains("openjml-lsp-esc-"));
            assertTrue("Callback URI must be a file:// URI: " + uri,
                    uri.startsWith("file:"));
        }
    }

    // -----------------------------------------------------------------------
    // Dirty file with package declaration
    // -----------------------------------------------------------------------

    /**
     * A dirty snapshot file that declares a package must be written to a
     * package-relative subdirectory in the temp dir. The run must complete
     * without errors, and any diagnostics must still be keyed by the real URI.
     */
    @Test
    public void testDirtyFileWithPackage() throws Exception {
        // Write a real file (no package — simplest on-disk layout for TemporaryFolder).
        File f = writeJava("EscCtxPkg.java",
                "public class EscCtxPkg {\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n");

        // Snapshot introduces a package declaration and a type error.
        String dirtyContent =
                "package com.example;\n" +
                "public class EscCtxPkg {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";

        CheckRunner.DirCheckResult result = CheckRunner.runEscDirWithContext(
                List.of(f.getAbsolutePath()),
                Map.of(fileUri(f), dirtyContent),
                new OpenJMLSettings(), null);

        assertNotNull("Expected non-null result for dirty file with package", result);
        // Verify no temp-path leaks in diagnostic keys.
        for (String key : result.diagnosticsByUri().keySet()) {
            assertFalse("Diagnostic key must not be a temp-dir path: " + key,
                    key.contains("openjml-lsp-esc-"));
        }
    }

    // -----------------------------------------------------------------------
    // uriToPath — basic unit tests (low-priority, in this class for convenience)
    // -----------------------------------------------------------------------

    @Test
    public void testUriToPathNormal() {
        String path = CheckRunner.uriToPath("file:///home/user/Foo.java");
        assertEquals("/home/user/Foo.java", path);
    }

    @Test
    public void testUriToPathWithEncodedSpaces() {
        String path = CheckRunner.uriToPath("file:///my%20dir/Foo.java");
        assertEquals("/my dir/Foo.java", path);
    }

    @Test
    public void testUriToPathMalformed() {
        String path = CheckRunner.uriToPath("not a valid uri :// !!!");
        assertNull("Expected null for malformed URI", path);
    }
}
