package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.DiagnosticConverter;
import org.openjml.lsp.OpenJMLCommands;

import java.io.File;
import java.io.FileWriter;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for per-method ESC marker publishing via
 * {@code openjml.runEsc} with an OS file PATH argument.
 *
 * <p>Eclipse triggers ESC by sending {@code openjml.runEsc} with the file's
 * OS path (not a {@code file://} URI).  This routes to
 * {@code scheduleEscForPaths} → {@code runEscDirWithContext} → per-method
 * callback → {@code updateEscStatusPartial} → end-of-run {@code updateEscStatus}
 * → {@code publishMerged} → {@code client.publishDiagnostics}.
 *
 * <p>The tests exercise the full chain and verify that ESC diagnostics
 * (source={@link DiagnosticConverter#SOURCE_ESC}) are actually delivered
 * to the client — the path that was broken when {@code updateEscStatus}
 * incorrectly preserved the empty {@code byUri} set by
 * {@code updateEscStatusPartial} rather than computing new diags from
 * {@code diagsByMethod}.
 */
public class EscPerMethodMarkerTest extends ProtocolTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    @Before
    @Override
    public void setUp() throws Exception {
        startServer();
    }

    @After
    @Override
    public void tearDown() {
        super.tearDown();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private File writeJava(String filename, String content) throws Exception {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    /** Open a file in the server and drain the --check notification it triggers. */
    private void didOpenAndDrainCheck(String uri, String source) throws Exception {
        didOpen(uri, source);
        nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
    }

    // -----------------------------------------------------------------------
    // (1) scheduleEscForPaths — failing method produces ESC diagnostics
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEsc} with an OS file path (not a URI) routes to
     * {@code scheduleEscForPaths}.  A method with {@code ensures false} must
     * produce at least one ESC diagnostic delivered via
     * {@code textDocument/publishDiagnostics}.
     *
     * <p>This is the code path Eclipse uses.  It was broken: {@code updateEscStatus}
     * preserved the empty {@code byUri} left by {@code updateEscStatusPartial}
     * instead of computing the actual method diagnostics, so {@code escDiags=0}
     * on every publish.
     */
    @Test
    public void testEscPathRoute_FailingMethodProducesDiagnostics() throws Exception {
        String source =
                "public class EscPathFail {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        File f   = writeJava("EscPathFail.java", source);
        String uri  = f.toPath().toUri().toString();   // file:///...
        String path = f.getAbsolutePath();              // OS path → scheduleEscForPaths

        didOpenAndDrainCheck(uri, source);

        // Send RUN_ESC with the OS path — this is what Eclipse sends.
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(path) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Must receive a publishDiagnostics notification with at least one ESC diagnostic.
        JsonObject note = nextNonEmptyDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("scheduleEscForPaths must publish ESC diagnostics for 'ensures false'",
                note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("At least one ESC diagnostic must be present", diags.isEmpty());

        // At least one diagnostic must have source = SOURCE_ESC.
        boolean hasEscSource = false;
        for (int i = 0; i < diags.size(); i++) {
            JsonObject d = diags.get(i).getAsJsonObject();
            if (d.has("source")
                    && DiagnosticConverter.SOURCE_ESC.equals(d.get("source").getAsString())) {
                hasEscSource = true;
                break;
            }
        }
        assertTrue("Diagnostics must include at least one with source=" + DiagnosticConverter.SOURCE_ESC,
                hasEscSource);
    }

    // -----------------------------------------------------------------------
    // (2) scheduleEscForPaths — verified method produces no failure diagnostics
    // -----------------------------------------------------------------------

    /**
     * A method with a satisfiable postcondition verified by ESC must produce
     * a {@code textDocument/publishDiagnostics} notification, and none of its
     * diagnostics should be error-severity ESC failures.
     */
    @Test
    public void testEscPathRoute_VerifiedMethodNoFailureDiagnostics() throws Exception {
        String source =
                "public class EscPathOk {\n"
                + "    //@ requires x >= 0 && x < 1000;\n"
                + "    //@ ensures \\result == x + 1;\n"
                + "    public int m(int x) { return x + 1; }\n"
                + "}\n";
        File f   = writeJava("EscPathOk.java", source);
        String uri  = f.toPath().toUri().toString();
        String path = f.getAbsolutePath();

        didOpenAndDrainCheck(uri, source);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(path) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Wait for any publishDiagnostics (the run must complete and publish).
        JsonObject note = nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("scheduleEscForPaths must publish diagnostics after ESC run", note);

        // There must be no error-severity ESC failure diagnostics for a verified method.
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        for (int i = 0; i < diags.size(); i++) {
            JsonObject d = diags.get(i).getAsJsonObject();
            if (d.has("source") &&
                    DiagnosticConverter.SOURCE_ESC.equals(d.get("source").getAsString())) {
                int severity = d.has("severity") ? d.get("severity").getAsInt() : 1;
                assertNotEquals(
                        "Verified method must not produce error-severity ESC diagnostics; got: "
                                + d.get("message").getAsString(),
                        1 /* Error */, severity);
            }
        }
    }

    // -----------------------------------------------------------------------
    // (3) scheduleEscForPaths — mixed file: failure diags for failing methods
    // -----------------------------------------------------------------------

    /**
     * A file with both verified and failing methods submitted via
     * {@code openjml.runEsc} with an OS path must deliver ESC failure
     * diagnostics for the failing method and no error-severity ESC diagnostics
     * for the verified method.
     */
    @Test
    public void testEscPathRoute_MixedMethods() throws Exception {
        String source =
                "public class EscPathMixed {\n"
                + "    //@ requires x >= 0 && x < 1000;\n"
                + "    //@ ensures \\result == x + 1;\n"
                + "    public int good(int x) { return x + 1; }\n"
                + "\n"
                + "    //@ ensures false;\n"
                + "    public int bad(int x) { return x; }\n"
                + "}\n";
        File f   = writeJava("EscPathMixed.java", source);
        String uri  = f.toPath().toUri().toString();
        String path = f.getAbsolutePath();

        didOpenAndDrainCheck(uri, source);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(path) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Must receive a publishDiagnostics with at least one ESC error.
        // The verified method may publish a Hint notification first — skip those.
        JsonObject note = nextEscErrorDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull(
                "Mixed-method ESC must publish a notification with an ESC error for 'bad'",
                note);
    }

    // -----------------------------------------------------------------------
    // (4) scheduleEscForUri — file URI route produces ESC diagnostics
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEsc} with a {@code file://} URI (not an OS path) routes to
     * {@code scheduleEscForUri} → {@code scheduleEscFile}.  A method with
     * {@code ensures false} must produce at least one ESC diagnostic.
     */
    @Test
    public void testEscUriRoute_FailingMethodProducesDiagnostics() throws Exception {
        String source =
                "public class EscUriFail {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        File f  = writeJava("EscUriFail.java", source);
        String uri = f.toPath().toUri().toString();   // file:///... → scheduleEscForUri

        didOpenAndDrainCheck(uri, source);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(uri) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        JsonObject note = nextNonEmptyDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("scheduleEscForUri must publish ESC diagnostics for 'ensures false'", note);

        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        boolean hasEscSource = false;
        for (int i = 0; i < diags.size(); i++) {
            JsonObject d = diags.get(i).getAsJsonObject();
            if (d.has("source")
                    && DiagnosticConverter.SOURCE_ESC.equals(d.get("source").getAsString())) {
                hasEscSource = true;
                break;
            }
        }
        assertTrue("URI-route ESC must deliver at least one diagnostic with source="
                + DiagnosticConverter.SOURCE_ESC, hasEscSource);
    }

    // -----------------------------------------------------------------------
    // (5) scheduleEscForPaths incremental: two failing methods → two separate
    //     non-empty publishDiagnostics notifications before the run finishes
    // -----------------------------------------------------------------------

    /**
     * With two failing methods, the server must deliver at least two separate
     * non-empty {@code textDocument/publishDiagnostics} notifications —
     * one after the first method's proof completes and another after the second.
     *
     * <p>Before the {@code updateEscStatusPartial} fix, every incremental
     * publish had {@code count=0} because {@code byUri} was never populated
     * during partial updates; only the single end-of-run {@code updateEscStatus}
     * call stored real diagnostics.  A test that only waits for <em>any</em>
     * non-empty notification cannot detect this regression.
     */
    @Test
    public void testEscPathRoute_IncrementalPublish_TwoFailingMethods() throws Exception {
        String source =
                "public class EscPathIncremental {\n"
                + "    //@ ensures false;\n"
                + "    public int failA(int x) { return x; }\n"
                + "\n"
                + "    //@ ensures false;\n"
                + "    public int failB(int x) { return x; }\n"
                + "}\n";
        File f   = writeJava("EscPathIncremental.java", source);
        String uri  = f.toPath().toUri().toString();
        String path = f.getAbsolutePath();

        didOpenAndDrainCheck(uri, source);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(path) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // With incremental publishing each failing method fires a separate
        // publishDiagnostics; we need at least 2 non-empty notifications.
        List<JsonObject> notes = collectNonEmptyDiagsForUri(uri, 2, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertTrue(
                "Incremental publishing (scheduleEscForPaths) must deliver at least 2 "
                + "separate non-empty publishDiagnostics notifications for a file with "
                + "2 failing methods, got: " + notes.size(),
                notes.size() >= 2);
    }

    // -----------------------------------------------------------------------
    // (6) scheduleEscForUri incremental: two failing methods → two separate
    //     non-empty publishDiagnostics notifications before the run finishes
    // -----------------------------------------------------------------------

    /**
     * Same incremental check as (5) but via the {@code file://} URI route
     * ({@code scheduleEscForUri} → {@code scheduleEscFile}).
     */
    @Test
    public void testEscUriRoute_IncrementalPublish_TwoFailingMethods() throws Exception {
        String source =
                "public class EscUriIncremental {\n"
                + "    //@ ensures false;\n"
                + "    public int failA(int x) { return x; }\n"
                + "\n"
                + "    //@ ensures false;\n"
                + "    public int failB(int x) { return x; }\n"
                + "}\n";
        File f  = writeJava("EscUriIncremental.java", source);
        String uri = f.toPath().toUri().toString();

        didOpenAndDrainCheck(uri, source);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(uri) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        List<JsonObject> notes = collectNonEmptyDiagsForUri(uri, 2, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertTrue(
                "Incremental publishing (scheduleEscForUri) must deliver at least 2 "
                + "separate non-empty publishDiagnostics notifications for a file with "
                + "2 failing methods, got: " + notes.size(),
                notes.size() >= 2);
    }

    // -----------------------------------------------------------------------
    // (7) scheduleEscForPaths incremental: verified method → Hint marker appears
    //     before end-of-run, not only in the final batch
    // -----------------------------------------------------------------------

    /**
     * A file with one verified and one failing method.  With the incremental
     * verified-hint fix, the "Verified" hint diagnostic (source=SOURCE_ESC,
     * severity=Hint) for the verified method must arrive in a
     * {@code publishDiagnostics} notification before the full run completes,
     * so Eclipse can show the green checkmark incrementally.
     *
     * <p>Without the fix, {@code updateEscStatusPartial} left {@code byUri}
     * empty for UNSAT methods, so no "Verified" hint was published until the
     * end-of-run {@code updateEscStatus} call.
     */
    @Test
    public void testEscPathRoute_IncrementalPublish_VerifiedHintAppearsIncrementally()
            throws Exception {
        String source =
                "public class EscPathVerifiedIncr {\n"
                + "    //@ requires x >= 0 && x < 1000;\n"
                + "    //@ ensures \\result == x + 1;\n"
                + "    public int good(int x) { return x + 1; }\n"
                + "\n"
                + "    //@ ensures false;\n"
                + "    public int bad(int x) { return x; }\n"
                + "}\n";
        File f   = writeJava("EscPathVerifiedIncr.java", source);
        String uri  = f.toPath().toUri().toString();
        String path = f.getAbsolutePath();

        didOpenAndDrainCheck(uri, source);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(path) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Need at least 2 non-empty notifications: one for the verified method
        // (carrying the "Verified" hint) and one for the failing method (error).
        List<JsonObject> notes = collectNonEmptyDiagsForUri(uri, 2, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertTrue(
                "Incremental publishing must deliver at least 2 non-empty notifications "
                + "for a file with one verified and one failing method, got: " + notes.size(),
                notes.size() >= 2);

        // Across all notifications there must be at least one Hint-severity SOURCE_ESC
        // diagnostic — the "Verified" marker for the good method.
        boolean hasVerifiedHint = false;
        outer:
        for (JsonObject note : notes) {
            JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
            for (int i = 0; i < diags.size(); i++) {
                JsonObject d = diags.get(i).getAsJsonObject();
                if (d.has("source")
                        && DiagnosticConverter.SOURCE_ESC.equals(d.get("source").getAsString())
                        && d.has("severity") && d.get("severity").getAsInt() == 4 /* Hint */) {
                    hasVerifiedHint = true;
                    break outer;
                }
            }
        }
        assertTrue("Incremental publish must include a Hint-severity 'Verified' marker "
                + "with source=" + DiagnosticConverter.SOURCE_ESC, hasVerifiedHint);
    }
}
