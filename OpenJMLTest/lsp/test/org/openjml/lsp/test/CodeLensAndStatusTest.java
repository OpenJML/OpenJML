package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;
import org.openjml.lsp.OpenJMLCommands;

import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for {@code textDocument/codeLens} responses and the ESC
 * status-badge lifecycle: UNKNOWN before ESC, VERIFIED after a successful proof,
 * and NOT_VERIFIED after a proof failure.
 *
 * <p>Each test drives an in-process LSP server via {@link RawLspClient} over
 * JSON-RPC pipes.  All three status values are exercised end-to-end through the
 * full server stack, complementing the direct-API coverage in
 * {@link EscStatusTest}.
 */
public class CodeLensAndStatusTest extends ProtocolTestBase {

    // -----------------------------------------------------------------------
    // UNKNOWN status — before any ESC run
    // -----------------------------------------------------------------------

    /**
     * After {@code textDocument/didOpen} and the resulting {@code --check}, all methods
     * must show the UNKNOWN status badge (ESC has never run).  The lens title must
     * contain the "Run ESC" indicator ({@code \u25b6} or the text "Run ESC").
     */
    @Test
    public void testCodeLensUnknownBeforeEsc() throws Exception {
        String uri    = "file:///CodeLensUnknown.java";
        String source = "public class CodeLensUnknown {\n"
                + "    public int add(int a, int b) { return a + b; }\n"
                + "}\n";
        didOpen(uri, source);
        // Drain the open-triggered --check notification.
        nextDiagsFor("CodeLensUnknown", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        JsonArray lenses = requestCodeLens(uri);
        assertNotNull("Expected code lenses for file with one method", lenses);
        assertFalse("Expected at least one code lens", lenses.isEmpty());
        String title = firstLensTitle(lenses);
        assertNotNull("Code lens must have a title", title);
        // UNKNOWN status title: "OpenJML: — ▶ Run ESC"
        assertTrue("UNKNOWN lens title must contain '▶' or 'Run ESC'; got: " + title,
                title.contains("\u25b6") || title.contains("Run ESC"));
    }

    // -----------------------------------------------------------------------
    // VERIFIED status — after successful ESC
    // -----------------------------------------------------------------------

    /**
     * After {@code openjml.runEsc} on a file with a trivially-true postcondition,
     * the code lens must show VERIFIED ({@code \u2713} or "Verified").
     */
    @Test
    public void testCodeLensVerifiedAfterEsc() throws Exception {
        String uri    = "file:///CodeLensVerified.java";
        String source = "public class CodeLensVerified {\n"
                + "    //@ ensures \\result >= 0;\n"
                + "    public int m() { return 42; }\n"
                + "}\n";
        didOpen(uri, source);
        // Drain the open-triggered --check notification.
        nextDiagsFor("CodeLensVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Run ESC on the URI (file:// prefix → uses in-memory content from lastContent).
        String argsJson = "[\"\",\"\",\"\",\"\",\"" + jsonEscape(uri) + "\"]";
        executeCommand(OpenJMLCommands.RUN_ESC, argsJson);

        // Wait for the ESC completion publishDiagnostics.
        JsonObject note = nextDiagsFor("CodeLensVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after ESC", note);

        // Poll code lenses until the status changes from UNKNOWN to VERIFIED.
        // updateEscStatus() happens before publishMerged() on the ESC thread, but there
        // can be a brief window where the codeLens handler is served before
        // methodEscStatus is visible from the LSP dispatch thread.
        // VERIFIED status title: "OpenJML: ✓ Verified ↺ Re-run"
        String title = pollLensTitleUntil(uri, "\u2713", 30);
        if (title == null) title = pollLensTitleUntil(uri, "Verified", 30);
        assertNotNull("Expected code lenses after ESC", title);
        assertTrue("VERIFIED lens title must contain '✓' or 'Verified'; got: " + title,
                title.contains("\u2713") || title.contains("Verified"));
    }

    // -----------------------------------------------------------------------
    // NOT_VERIFIED status — after ESC finds a verification failure
    // -----------------------------------------------------------------------

    /**
     * After {@code openjml.runEsc} on a method with {@code ensures false}, the
     * code lens must show NOT_VERIFIED ({@code \u2717} or "Not verified").
     */
    @Test
    public void testCodeLensNotVerifiedAfterEsc() throws Exception {
        String uri    = "file:///CodeLensNotVerified.java";
        String source = "public class CodeLensNotVerified {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        didOpen(uri, source);
        // Drain the open-triggered --check notification (no type errors for valid JML syntax).
        nextDiagsFor("CodeLensNotVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Run ESC on the URI.
        String argsJson = "[\"\",\"\",\"\",\"\",\"" + jsonEscape(uri) + "\"]";
        executeCommand(OpenJMLCommands.RUN_ESC, argsJson);

        // Wait for the ESC failure publishDiagnostics (skip any intermediate empty notifications
        // from RUNNING events, which are sent before the proof result is available).
        JsonObject note = nextNonEmptyDiagsFor("CodeLensNotVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected non-empty publishDiagnostics after ESC", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one ESC diagnostic for 'ensures false'", diags.isEmpty());

        // Poll code lenses until the status changes from UNKNOWN to NOT_VERIFIED.
        // NOT_VERIFIED status title: "OpenJML: ✗ Not verified (N issues)"
        String title = pollLensTitleUntil(uri, "\u2717", 30);
        if (title == null) title = pollLensTitleUntil(uri, "Not verified", 30);
        assertNotNull("Expected code lenses after ESC failure", title);
        assertTrue("NOT_VERIFIED lens title must contain '✗' or 'Not verified'; got: " + title,
                title.contains("\u2717") || title.contains("Not verified"));
    }
}
