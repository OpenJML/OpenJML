package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.OpenJMLCommands;

import java.io.File;
import java.io.FileWriter;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for {@code textDocument/didClose} semantics.
 *
 * <p>Closing an editor must:
 * <ul>
 *   <li>Clear the dirty mark and in-memory editor buffer.</li>
 *   <li>Retain all diagnostics in the client's Problems panel.</li>
 *   <li>Not cancel any pending or running checks — project-level analysis
 *       continues regardless of whether the file is open in an editor.</li>
 *   <li>Retain proof results — ESC results are project-level, not editor-level.
 *       When the file is re-opened the retained results appear immediately
 *       without requiring another ESC run.</li>
 * </ul>
 */
public class DidCloseTest extends ProtocolTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    @Before
    @Override
    public void setUp() throws Exception {
        startServer();
    }

    private File writeJava(String filename, String content) throws Exception {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    // -----------------------------------------------------------------------
    // (1) Diagnostics are retained after close
    // -----------------------------------------------------------------------

    /**
     * After a file with a type error is opened and checked, closing the editor
     * must not clear the diagnostics from the client's Problems panel.
     * The server must not publish an empty diagnostic list on didClose.
     */
    @Test
    public void testDiagnosticsRetainedAfterClose() throws Exception {
        String uri    = "file:///DidCloseRetainDiags.java";
        String source =
                "public class DidCloseRetainDiags {\n"
                + "    public int m() { return \"wrong type\"; }\n"
                + "}\n";

        didOpen(uri, source);
        JsonObject diags = nextNonEmptyDiagsFor("DidCloseRetainDiags", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected diagnostics after open", diags);

        didClose(uri);

        // The server must NOT publish empty diagnostics on close.
        // Poll for a short window; any publishDiagnostics for this URI would be a bug.
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(SHORT_TIMEOUT);
        while (System.nanoTime() < deadline) {
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", 200, TimeUnit.MILLISECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            if (params.get("uri").getAsString().equals(uri)) {
                JsonArray arr = params.getAsJsonArray("diagnostics");
                assertFalse(
                        "Server must not publish empty diagnostics on didClose; got: " + arr,
                        arr.isEmpty());
            }
        }
    }

    // -----------------------------------------------------------------------
    // (2) Proof results retained after close — visible on re-open
    // -----------------------------------------------------------------------

    /**
     * After a file-level ESC run produces a VERIFIED code lens, closing and
     * re-opening the editor must show the VERIFIED lens immediately — the stored
     * proof result survives the close and is applied to the new code lenses
     * without requiring another ESC run.
     */
    @Test
    public void testProofResultsRetainedAfterClose() throws Exception {
        String source =
                "public class DidCloseRetainProof {\n"
                + "    //@ ensures \\result == x;\n"
                + "    public int id(int x) { return x; }\n"
                + "}\n";
        File f   = writeJava("DidCloseRetainProof.java", source);
        String uri = f.toPath().toUri().toString();

        didOpen(uri, source);
        nextDiagsFor("DidCloseRetainProof", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Run file ESC and wait for a VERIFIED lens.
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC + "\","
                + "\"arguments\":[\"\",\"" + jsonEscape(uri) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        nextNonEmptyDiagsFor("DidCloseRetainProof", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        String titleBefore = pollLensTitleUntil(uri, "\u2713", 60);
        assertNotNull("Expected VERIFIED lens before close", titleBefore);

        // Close then re-open the file.
        didClose(uri);
        didOpen(uri, source);
        nextDiagsFor("DidCloseRetainProof", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // The VERIFIED lens must reappear immediately from the retained proof result —
        // no ESC run has been submitted since the re-open.
        String titleAfter = pollLensTitleUntil(uri, "\u2713", 10);
        assertNotNull("Proof result must survive didClose; no VERIFIED lens after re-open", titleAfter);
        assertTrue("VERIFIED lens must still show \u2713; got: " + titleAfter,
                titleAfter.contains("\u2713") || titleAfter.contains("Verified"));
    }

    // -----------------------------------------------------------------------
    // (3) ESC run started before close completes after close
    // -----------------------------------------------------------------------

    /**
     * An ESC run submitted just before the editor is closed must complete
     * normally — didClose must not cancel running checks.  Re-opening the file
     * afterwards shows the VERIFIED lens from the completed run.
     */
    @Test
    public void testEscRunCompletesAfterClose() throws Exception {
        String source =
                "public class DidCloseEscContinues {\n"
                + "    //@ ensures \\result == x;\n"
                + "    public int id(int x) { return x; }\n"
                + "}\n";
        File f   = writeJava("DidCloseEscContinues.java", source);
        String uri = f.toPath().toUri().toString();

        didOpen(uri, source);
        nextDiagsFor("DidCloseEscContinues", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Submit ESC but do NOT wait for it to complete before closing.
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC + "\","
                + "\"arguments\":[\"\",\"" + jsonEscape(uri) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Close the editor immediately.
        didClose(uri);

        // Wait for the ESC run to complete (it must not have been cancelled).
        // Then re-open and verify the VERIFIED lens appears from the stored result.
        Thread.sleep(5000); // allow the in-flight ESC to finish
        didOpen(uri, source);
        nextDiagsFor("DidCloseEscContinues", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        String title = pollLensTitleUntil(uri, "\u2713", 60);
        assertNotNull("ESC run must complete after didClose and produce a VERIFIED lens on re-open", title);
        assertTrue("VERIFIED lens must contain \u2713; got: " + title,
                title.contains("\u2713") || title.contains("Verified"));
    }
}
