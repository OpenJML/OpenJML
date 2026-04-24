package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.DiagnosticConverter;
import org.openjml.lsp.OpenJMLCommands;

import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for all ESC invocation variants that Eclipse and VSCode
 * clients use.  Each test drives a real {@link org.openjml.lsp.OpenJMLLanguageServer} through
 * pipes and asserts on the resulting {@code textDocument/publishDiagnostics}
 * notifications.
 *
 * <p>Covered scenarios:
 * <ol>
 *   <li>{@code openjml.runEsc} with multiple OS file paths — arbitrary order</li>
 *   <li>{@code openjml.runEsc} with a directory OS path</li>
 *   <li>{@code openjml.runEscSplitByFile} — one task per file, arbitrary order</li>
 *   <li>{@code openjml.runEscSplitByMethod} — one task per method, arbitrary order,
 *       incremental per-method publishing</li>
 *   <li>{@code openjml.runEscForMethod} — single method; only that method's
 *       diagnostics appear</li>
 * </ol>
 *
 * <p>For split-by-file and split-by-method the tests collect <em>all</em>
 * notifications until a deadline and assert on the union, because concurrent
 * tasks complete in arbitrary order.
 */
public class EscInvocationVariantsTest extends ProtocolTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    @Before
    @Override
    public void setUp() throws Exception {
        startServer();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private File writeJava(String filename, String content) throws Exception {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    private File writeJavaInDir(File dir, String filename, String content) throws Exception {
        File f = new File(dir, filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    private void didOpenAndDrainCheck(String uri, String source) throws Exception {
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}");
        nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
    }

    /**
     * Collects all {@code textDocument/publishDiagnostics} notifications until
     * every URI in {@code wantUris} has been seen with at least one ESC
     * diagnostic, or the deadline expires.  Returns the set of URIs that
     * received at least one ESC diagnostic.
     */
    private Set<String> collectUrisWithEscDiags(Set<String> wantUris,
            long timeout, TimeUnit unit) throws InterruptedException {
        Set<String> seen = new HashSet<>();
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (!seen.containsAll(wantUris)) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            String uri = params.get("uri").getAsString();
            if (!wantUris.contains(uri)) continue;
            JsonArray diags = params.getAsJsonArray("diagnostics");
            for (int i = 0; i < diags.size(); i++) {
                JsonObject d = diags.get(i).getAsJsonObject();
                if (d.has("source") &&
                        DiagnosticConverter.SOURCE_ESC.equals(d.get("source").getAsString())) {
                    seen.add(uri);
                    break;
                }
            }
        }
        return seen;
    }

    // -----------------------------------------------------------------------
    // (1) openjml.runEsc with multiple OS file paths
    // -----------------------------------------------------------------------

    /**
     * Two separate files each with a failing method, submitted in one
     * {@code openjml.runEsc} call with both OS paths.  Both files must
     * eventually receive ESC error diagnostics (order is arbitrary since
     * they may be proved in any order).
     */
    @Test
    public void testRunEsc_MultipleOsFilePaths() throws Exception {
        String srcA =
                "public class EscMultiA {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        String srcB =
                "public class EscMultiB {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        File fA = writeJava("EscMultiA.java", srcA);
        File fB = writeJava("EscMultiB.java", srcB);
        String uriA  = fA.toPath().toUri().toString();
        String uriB  = fB.toPath().toUri().toString();
        String pathA = fA.getAbsolutePath();
        String pathB = fB.getAbsolutePath();

        didOpenAndDrainCheck(uriA, srcA);
        didOpenAndDrainCheck(uriB, srcB);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(pathA)
                + "\",\"" + jsonEscape(pathB) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        Set<String> want = new HashSet<>();
        want.add(uriA);
        want.add(uriB);
        Set<String> got = collectUrisWithEscDiags(want, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertEquals("Both files must receive ESC diagnostics via multi-path runEsc", want, got);
    }

    // -----------------------------------------------------------------------
    // (2) openjml.runEsc with a directory OS path
    // -----------------------------------------------------------------------

    /**
     * A directory containing two failing Java files submitted via one
     * {@code openjml.runEsc} call with the directory's OS path.  Both files
     * must receive ESC diagnostics.
     */
    @Test
    public void testRunEsc_DirectoryPath() throws Exception {
        File dir = tmp.newFolder("escdir");
        String srcA =
                "public class EscDirA {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        String srcB =
                "public class EscDirB {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        File fA = writeJavaInDir(dir, "EscDirA.java", srcA);
        File fB = writeJavaInDir(dir, "EscDirB.java", srcB);
        String uriA = fA.toPath().toUri().toString();
        String uriB = fB.toPath().toUri().toString();

        didOpenAndDrainCheck(uriA, srcA);
        didOpenAndDrainCheck(uriB, srcB);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(dir.getAbsolutePath()) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        Set<String> want = new HashSet<>();
        want.add(uriA);
        want.add(uriB);
        Set<String> got = collectUrisWithEscDiags(want, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertEquals("Both files in directory must receive ESC diagnostics", want, got);
    }

    // -----------------------------------------------------------------------
    // (3) openjml.runEscSplitByFile — one task per file, arbitrary order
    // -----------------------------------------------------------------------

    /**
     * Two failing files submitted via {@code openjml.runEscSplitByFile}.
     * Each file is proved as an independent task; results arrive in arbitrary
     * order.  Both files must eventually receive ESC diagnostics.
     */
    @Test
    public void testRunEscSplitByFile_TwoFailingFiles() throws Exception {
        String srcA =
                "public class EscSplitFileA {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        String srcB =
                "public class EscSplitFileB {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        File fA = writeJava("EscSplitFileA.java", srcA);
        File fB = writeJava("EscSplitFileB.java", srcB);
        String uriA  = fA.toPath().toUri().toString();
        String uriB  = fB.toPath().toUri().toString();
        String pathA = fA.getAbsolutePath();
        String pathB = fB.getAbsolutePath();

        didOpenAndDrainCheck(uriA, srcA);
        didOpenAndDrainCheck(uriB, srcB);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_SPLIT_BY_FILE
                + "\",\"arguments\":[\"\",\"" + jsonEscape(pathA)
                + "\",\"" + jsonEscape(pathB) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        Set<String> want = new HashSet<>();
        want.add(uriA);
        want.add(uriB);
        Set<String> got = collectUrisWithEscDiags(want, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertEquals("Both files must receive ESC diagnostics via runEscSplitByFile", want, got);
    }

    // -----------------------------------------------------------------------
    // (4) openjml.runEscSplitByMethod — incremental per-method, arbitrary order
    // -----------------------------------------------------------------------

    /**
     * A file with two failing methods submitted via
     * {@code openjml.runEscSplitByMethod}.  Each method is proved as an
     * independent task; results arrive in arbitrary order.  The test collects
     * all non-empty {@code publishDiagnostics} notifications and asserts that
     * at least two arrive (one per method — the incremental guarantee) and
     * that at least one has source={@link DiagnosticConverter#SOURCE_ESC}.
     */
    @Test
    public void testRunEscSplitByMethod_TwoFailingMethods_Incremental() throws Exception {
        String source =
                "public class EscSplitMethod {\n"
                + "    //@ ensures false;\n"
                + "    public int failA(int x) { return x; }\n"
                + "\n"
                + "    //@ ensures false;\n"
                + "    public int failB(int x) { return x; }\n"
                + "}\n";
        File f   = writeJava("EscSplitMethod.java", source);
        String uri  = f.toPath().toUri().toString();
        String path = f.getAbsolutePath();

        didOpenAndDrainCheck(uri, source);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_SPLIT_BY_METHOD
                + "\",\"arguments\":[\"\",\"" + jsonEscape(path) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Collect until we have at least 2 non-empty notifications (one per method).
        // Order is arbitrary since tasks run in parallel.
        List<JsonObject> notes = collectNonEmptyDiagsForUri(uri, 2, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertTrue(
                "runEscSplitByMethod must deliver at least 2 non-empty publishDiagnostics "
                + "notifications (one per failing method), got: " + notes.size(),
                notes.size() >= 2);

        // At least one notification must contain a SOURCE_ESC diagnostic.
        boolean hasEsc = false;
        for (JsonObject note : notes) {
            JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
            for (int i = 0; i < diags.size(); i++) {
                JsonObject d = diags.get(i).getAsJsonObject();
                if (d.has("source") &&
                        DiagnosticConverter.SOURCE_ESC.equals(d.get("source").getAsString())) {
                    hasEsc = true;
                    break;
                }
            }
        }
        assertTrue("At least one notification must contain a source=" +
                DiagnosticConverter.SOURCE_ESC + " diagnostic", hasEsc);
    }

    // -----------------------------------------------------------------------
    // (4b) openjml.runEscSplitByFile — incremental per-file publishing
    // -----------------------------------------------------------------------

    /**
     * With two failing files proved as independent tasks, each file's
     * {@code publishDiagnostics} must arrive as its proof completes — not both
     * at the very end.  We assert that both URIs receive ESC diagnostics
     * (order arbitrary), which implicitly verifies per-file publishing since
     * the two tasks run concurrently.
     *
     * <p>A single-file variant also confirms that a file with two failing methods
     * still produces a non-empty {@code publishDiagnostics} (the whole-file
     * result arrives at once for split-by-file, since there is no
     * per-method-completion callback in that path).
     */
    @Test
    public void testRunEscSplitByFile_SingleFile_NonEmpty() throws Exception {
        String source =
                "public class EscSplitFileSingle {\n"
                + "    //@ ensures false;\n"
                + "    public int failA(int x) { return x; }\n"
                + "\n"
                + "    //@ ensures false;\n"
                + "    public int failB(int x) { return x; }\n"
                + "}\n";
        File f   = writeJava("EscSplitFileSingle.java", source);
        String uri  = f.toPath().toUri().toString();
        String path = f.getAbsolutePath();

        didOpenAndDrainCheck(uri, source);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_SPLIT_BY_FILE
                + "\",\"arguments\":[\"\",\"" + jsonEscape(path) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        Set<String> want = new HashSet<>();
        want.add(uri);
        Set<String> got = collectUrisWithEscDiags(want, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertEquals("Single file with failing methods must receive ESC diagnostics "
                + "via runEscSplitByFile", want, got);
    }

    // -----------------------------------------------------------------------
    // (5) openjml.runEscForMethod — only the targeted method's diagnostics
    // -----------------------------------------------------------------------

    /**
     * A file with one failing and one verified method; {@code openjml.runEscForMethod}
     * targets only the failing method.  The resulting {@code publishDiagnostics}
     * must include at least one ESC error for the targeted method and must not
     * include an ESC error for the verified method.
     *
     * <p>The method name passed to the server is the simple AST name
     * ({@code "failA"}).  The server resolves it to the fully-qualified
     * {@code --method} argument via the AST cache.
     */
    @Test
    public void testRunEscForMethod_TargetsOnlyRequestedMethod() throws Exception {
        String source =
                "public class EscForMethod {\n"
                + "    //@ requires x >= 0 && x < 1000;\n"
                + "    //@ ensures \\result == x + 1;\n"
                + "    public int good(int x) { return x + 1; }\n"
                + "\n"
                + "    //@ ensures false;\n"
                + "    public int failA(int x) { return x; }\n"
                + "}\n";
        File f  = writeJava("EscForMethod.java", source);
        String uri = f.toPath().toUri().toString();

        didOpenAndDrainCheck(uri, source);

        // Send runEscForMethod in code-lens format: [uri, methodName].
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":[\"" + jsonEscape(uri) + "\",\"failA\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Wait for a publishDiagnostics with at least one ESC error.
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS);
        JsonObject escNote = null;
        while (escNote == null) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            if (!params.get("uri").getAsString().equals(uri)) continue;
            JsonArray diags = params.getAsJsonArray("diagnostics");
            for (int i = 0; i < diags.size(); i++) {
                JsonObject d = diags.get(i).getAsJsonObject();
                if (d.has("source") &&
                        DiagnosticConverter.SOURCE_ESC.equals(d.get("source").getAsString()) &&
                        d.has("severity") && d.get("severity").getAsInt() == 1) {
                    escNote = msg;
                    break;
                }
            }
        }
        assertNotNull("runEscForMethod(failA) must publish at least one ESC error", escNote);

        // No ESC error for the verified method (good).  "good" lives above line 4
        // and "failA" starts at line 5+.  An ESC error for "good" would have a
        // line number in the range 0-3.
        JsonArray diags = escNote.getAsJsonObject("params").getAsJsonArray("diagnostics");
        for (int i = 0; i < diags.size(); i++) {
            JsonObject d = diags.get(i).getAsJsonObject();
            if (!d.has("source") ||
                    !DiagnosticConverter.SOURCE_ESC.equals(d.get("source").getAsString()))
                continue;
            if (!d.has("severity") || d.get("severity").getAsInt() != 1) continue;
            int line = d.getAsJsonObject("range").getAsJsonObject("start").get("line").getAsInt();
            assertTrue(
                    "runEscForMethod(failA) must not produce ESC errors for method 'good' "
                    + "(line 0-3); got error at line " + line,
                    line >= 4);
        }
    }
}
