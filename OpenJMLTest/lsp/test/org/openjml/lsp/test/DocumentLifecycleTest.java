package org.openjml.lsp.test;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for the document-lifecycle notifications:
 * {@code textDocument/didOpen}, {@code textDocument/didChange}, and
 * {@code textDocument/didClose}.
 *
 * <p>Each test drives an in-process LSP server through the full JSON-RPC path
 * via {@link RawLspClient} and asserts on the resulting
 * {@code textDocument/publishDiagnostics} notifications.  This verifies that
 * the server's document-tracking wiring (content storage, scheduler dispatch)
 * is intact end-to-end, complementing the direct-API tests in
 * {@link DiagnosticsTest}.
 */
public class DocumentLifecycleTest extends ProtocolTestBase {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private void openDocumentFile(String uri, String source) throws Exception {
        Gson gson = new Gson();
        String params = "{\"textDocument\":{\"uri\":" + gson.toJson(uri) + ","
                + "\"languageId\":\"java\",\"version\":1,\"text\":"
                + gson.toJson(source) + "}}";
        client.sendNotification("textDocument/didOpen", params);
    }

    private static Path testdataFile(String relative) {
        String root = System.getProperty("lsp.testdata");
        if (root == null) throw new IllegalStateException("System property lsp.testdata must be set");
        return Paths.get(root).resolve(relative);
    }

    // -----------------------------------------------------------------------
    // textDocument/didOpen
    // -----------------------------------------------------------------------

    /**
     * {@code textDocument/didOpen} with a type-error source must trigger
     * {@code textDocument/publishDiagnostics} containing Error-severity diagnostics.
     */
    @Test
    public void testDidOpenErrorTriggersPublishDiagnostics() throws Exception {
        String uri = "file:///DLCOpenErr.java";
        String source =
                "public class DLCOpenErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";
        didOpen(uri, source);

        JsonObject note = nextDiagsFor("DLCOpenErr", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen of erroneous file", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one diagnostic", diags.isEmpty());
    }

    /**
     * {@code textDocument/didOpen} with clean Java source must trigger
     * {@code textDocument/publishDiagnostics} with an empty diagnostics array.
     */
    @Test
    public void testDidOpenCleanFilePublishesEmptyDiagnostics() throws Exception {
        String uri = "file:///DLCOpenClean.java";
        String source =
                "public class DLCOpenClean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n";
        didOpen(uri, source);

        JsonObject note = nextDiagsFor("DLCOpenClean", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen of clean file", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("Expected empty diagnostics for clean file", diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // textDocument/completion
    // -----------------------------------------------------------------------

    /**
     * Sending {@code textDocument/completion} with the cursor inside a JML
     * annotation ({@code //@ req}) must return a non-empty list of completion
     * items that includes {@code requires}.  This exercises the wiring in
     * {@link org.openjml.lsp.OpenJMLTextDocumentService#completion} and confirms
     * that the server advertises and correctly routes completion requests.
     *
     * <p>The response {@code result} may be a JSON array (list form) or a JSON
     * object with an {@code items} array (CompletionList form); both are handled.
     */
    @Test
    public void testCompletionInsideJmlAnnotationReturnsKeywords() throws Exception {
        String uri = "file:///DLCCompletion.java";
        // line 0: "public class DLCCompletion {"
        // line 1: "    //@ req"   ← cursor at end (col 11), inside JML annotation
        // line 2: "    public void m() {}"
        // line 3: "}"
        String source =
                "public class DLCCompletion {\n" +
                "    //@ req\n" +
                "    public void m() {}\n" +
                "}\n";
        didOpen(uri, source);
        // Drain the initial publishDiagnostics before sending the completion request
        // so it does not interfere with the response queue.
        nextDiagsFor("DLCCompletion", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Send textDocument/completion: cursor at line 1, col 11 (end of "//@ req")
        String params =
                "{\"textDocument\":{\"uri\":\"" + uri + "\"}," +
                "\"position\":{\"line\":1,\"character\":11}," +
                "\"context\":{\"triggerKind\":1}}";
        client.sendRequest("textDocument/completion", params);

        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to textDocument/completion", resp);
        assertTrue("Response must have a result field", resp.has("result"));

        // result may be an array (List<CompletionItem>) or object (CompletionList)
        JsonElement result = resp.get("result");
        JsonArray items;
        if (result.isJsonArray()) {
            items = result.getAsJsonArray();
        } else {
            items = result.getAsJsonObject().getAsJsonArray("items");
        }
        assertNotNull("Completion result must contain an items array", items);
        assertFalse("Expected at least one completion item inside JML annotation", items.isEmpty());

        boolean hasRequires = false;
        for (JsonElement el : items) {
            if ("requires".equals(el.getAsJsonObject().get("label").getAsString())) {
                hasRequires = true;
                break;
            }
        }
        assertTrue("'requires' must appear in completions inside a JML annotation", hasRequires);
    }

    // -----------------------------------------------------------------------
    // dirty-file lifecycle: dirtyUris tracking across didChange / didSave
    // -----------------------------------------------------------------------

    /**
     * Opening a clean disk file and then changing it (making it dirty) must
     * cause subsequent checks to use the in-memory (dirty) content rather than
     * the on-disk content.
     *
     * <p>The disk file ({@code testDirtyLifecycle/LifecycleClean.java}) has no
     * type errors.  After {@code didChange} introduces a type error, the server
     * marks the URI dirty (adds it to {@code dirtyUris}) and the triggered
     * {@code --check} must pick up the dirty content and publish an error diagnostic.
     *
     * <p>Test data: {@code testdata/testDirtyLifecycle/LifecycleClean.java}
     */
    @Test
    public void testDirtyDiskFile_CheckUsesDirtyContent() throws Exception {
        Path file = testdataFile("testDirtyLifecycle/LifecycleClean.java");
        String uri = file.toUri().toString();

        // Open the clean disk file — expect empty diagnostics.
        openDocumentFile(uri, Files.readString(file));
        JsonObject openNote = nextDiagsFor("LifecycleClean", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen of clean disk file", openNote);
        assertTrue("Expected no diagnostics for clean disk file on open",
                openNote.getAsJsonObject("params").getAsJsonArray("diagnostics").isEmpty());

        // Change the file to introduce a type error — URI now in dirtyUris.
        String errSource =
                "public class LifecycleClean {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";
        didChange(uri, 2, errSource);

        // The check triggered by didChange must use the dirty (in-memory) content.
        JsonObject changeNote = nextDiagsFor("LifecycleClean", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didChange", changeNote);
        JsonArray diags = changeNote.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected type-error diagnostic: dirty content must be used, not clean disk",
                diags.isEmpty());
    }

    /**
     * After {@code didSave}, the URI is removed from {@code dirtyUris} but
     * {@code lastContent} still holds the saved content (the editor buffer that
     * was written to disk).  The save-triggered {@code --check} must use that
     * content and publish the same diagnostics as the preceding dirty check.
     *
     * <p>This verifies that {@code didSave} triggers a check and that the check
     * runs against the current (saved) content rather than silently disappearing.
     * The error introduced by {@code didChange} is still present in both the
     * editor buffer and on disk after the save; the diagnostic must persist.
     *
     * <p>Test data: {@code testdata/testDirtyLifecycle/LifecycleClean.java}
     */
    @Test
    public void testSaveAfterDirtyChange_CheckTriggeredWithCurrentContent() throws Exception {
        Path file = testdataFile("testDirtyLifecycle/LifecycleClean.java");
        String uri = file.toUri().toString();

        // Open the clean disk file — drain the initial empty diagnostics.
        openDocumentFile(uri, Files.readString(file));
        nextDiagsFor("LifecycleClean", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Introduce a type error — URI enters dirtyUris; check reports the error.
        String errSource =
                "public class LifecycleClean {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";
        didChange(uri, 2, errSource);
        JsonObject changeNote = nextDiagsFor("LifecycleClean", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected error diagnostics after didChange", changeNote);
        assertFalse("Expected at least one diagnostic after didChange",
                changeNote.getAsJsonObject("params").getAsJsonArray("diagnostics").isEmpty());

        // Save — URI removed from dirtyUris; server schedules a check using the
        // saved content (lastContent still holds the error, same as what's on disk now).
        didSave(uri);

        // The save-triggered check must run and report the same error.
        JsonObject saveNote = nextDiagsFor("LifecycleClean", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didSave", saveNote);
        assertFalse("Expected error diagnostic after save: saved content still has the type error",
                saveNote.getAsJsonObject("params").getAsJsonArray("diagnostics").isEmpty());
    }

    /**
     * Changing a previously clean file to introduce a type error must trigger
     * a new {@code textDocument/publishDiagnostics} with error diagnostics.
     */
    @Test
    public void testDidChangeIntroducingErrorTriggersDiagnostics() throws Exception {
        String uri = "file:///DLCChange.java";

        // Open clean — consume the initial empty publishDiagnostics
        String cleanSource =
                "public class DLCChange {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n";
        didOpen(uri, cleanSource);
        nextDiagsFor("DLCChange", TIMEOUT_SECONDS, TimeUnit.SECONDS); // drain initial publish

        // Change to a type error
        String errSource =
                "public class DLCChange {\n" +
                "    public int add(int a, int b) { return \"wrong\"; }\n" +
                "}\n";
        didChange(uri, 2, errSource);

        JsonObject note = nextDiagsFor("DLCChange", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didChange introducing error", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one error diagnostic after change", diags.isEmpty());
    }
}
