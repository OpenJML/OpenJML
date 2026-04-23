package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.OpenJMLCommands;
import org.openjml.lsp.OpenJMLLanguageServer;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer smoke tests for the unified {@code workspace/executeCommand}
 * argument encoding.
 *
 * <p>All commands share a fixed 4-element prefix at positions 0–3:
 * <pre>
 *   args[0] sourcePath     (empty = use server default)
 *   args[1] classPath      (empty = use server default)
 *   args[2] specsPath      (empty = use server default)
 *   args[3] propertiesFile (empty = none)
 * </pre>
 * Command-specific arguments follow at position 4+.
 *
 * <p>One test per major command is sufficient to confirm the JSON-RPC dispatch
 * wiring is intact.  Detailed behavioural coverage lives in the direct-API
 * tests ({@link CheckRunnerDirTest}, {@link DiagnosticsTest}, etc.).
 */
public class CommandDispatchTest {

    private static final long TIMEOUT_SECONDS      = 120;
    private static final long SHORT_TIMEOUT_SECONDS = 5;

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    private OpenJMLLanguageServer server;
    private RawLspClient          client;

    // -----------------------------------------------------------------------
    // Setup / teardown
    // -----------------------------------------------------------------------

    @Before
    public void setUp() throws Exception {
        PipedInputStream  serverIn  = new PipedInputStream(65536);
        PipedOutputStream clientOut = new PipedOutputStream(serverIn);
        PipedInputStream  clientIn  = new PipedInputStream(65536);
        PipedOutputStream serverOut = new PipedOutputStream(clientIn);

        server = new OpenJMLLanguageServer();
        var launcher = LSPLauncher.createServerLauncher(server, serverIn, serverOut);
        server.connect(launcher.getRemoteProxy());
        launcher.startListening();

        client = new RawLspClient(clientOut, clientIn);

        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,\"capabilities\":{}}");
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Server must respond to initialize", resp);
        client.sendNotification("initialized", "{}");
    }

    @After
    public void tearDown() {
        if (client != null) client.stop();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private File writeJava(String filename, String content) throws IOException {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    private static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    private void sendCommand(String command, String argsJson) throws IOException {
        String params = "{\"command\":\"" + command + "\",\"arguments\":" + argsJson + "}";
        client.sendRequest("workspace/executeCommand", params);
    }

    private JsonObject nextDiagsContaining(String uriFragment, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            if (msg.getAsJsonObject("params").get("uri").getAsString().contains(uriFragment))
                return msg;
        }
    }

    /** Like {@link #nextDiagsContaining} but skips notifications with an empty diagnostics array. */
    private JsonObject nextNonEmptyDiagsContaining(String uriFragment, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            JsonObject params = msg.getAsJsonObject("params");
            if (!params.get("uri").getAsString().contains(uriFragment)) continue;
            if (!params.getAsJsonArray("diagnostics").isEmpty()) return msg;
        }
    }

    private static boolean hasError(JsonArray diags) {
        for (var el : diags) {
            JsonObject d = el.getAsJsonObject();
            if (d.has("severity") && d.get("severity").getAsInt() == 1) return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // openjml.checkJML — wiring smoke test
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.checkJML ["","","","", filePath]} must reach
     * {@link org.openjml.lsp.OpenJMLTextDocumentService#scheduleCheckForPaths}
     * and publish Error-severity diagnostics for a file with a type error.
     */
    @Test
    public void testCheckJmlCommandDispatch() throws Exception {
        File f = writeJava("CmdCheckErr.java",
                "public class CmdCheckErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        String argsJson = "[\"\",\"\",\"\",\"\",\"" + jsonEscape(f.getAbsolutePath()) + "\"]";
        sendCommand(OpenJMLCommands.CHECK_JML, argsJson);

        JsonObject note = nextDiagsContaining("CmdCheckErr", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics for CmdCheckErr.java", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one diagnostic", diags.isEmpty());
        assertTrue("Expected Error-severity diagnostic", hasError(diags));
    }

    // -----------------------------------------------------------------------
    // openjml.runEsc — wiring smoke test
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEsc ["","","","", filePath]} must reach
     * {@link org.openjml.lsp.OpenJMLTextDocumentService#scheduleEscForPaths}
     * and publish an ESC diagnostic for a method with {@code ensures false}.
     */
    @Test
    public void testRunEscCommandDispatch() throws Exception {
        File f = writeJava("CmdEscFail.java",
                "public class CmdEscFail {\n" +
                "    //@ ensures false;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n");

        String argsJson = "[\"\",\"\",\"\",\"\",\"" + jsonEscape(f.getAbsolutePath()) + "\"]";
        sendCommand(OpenJMLCommands.RUN_ESC, argsJson);

        JsonObject note = nextNonEmptyDiagsContaining("CmdEscFail", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected non-empty publishDiagnostics for CmdEscFail.java", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one ESC diagnostic for 'ensures false'", diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // openjml.checkJML — dirty in-memory content
    // -----------------------------------------------------------------------

    /**
     * When a file is open in the editor with dirty in-memory content (unsaved edits)
     * and {@code openjml.checkJML} is run on that file's OS path, the diagnostics
     * must reflect the dirty content rather than the clean on-disk version.
     *
     * <p>Setup: disk file is clean; the editor opens it with dirty (error) content.
     * The open-triggered {@code --check} reads from disk (clean), publishing no
     * diagnostics.  The subsequent {@code openjml.checkJML} command must snapshot
     * the dirty in-memory content and produce error diagnostics.
     */
    @Test
    public void testCheckJmlCommandUsesDirtyEditorContent() throws Exception {
        // File on disk: clean (no errors).
        File f = writeJava("CmdDirtyCheck.java",
                "public class CmdDirtyCheck {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        String uri = f.toPath().toUri().toString();

        // Open the file with its clean disk content.
        String openParams = "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(Files.readString(f.toPath())) + "\"}}";
        client.sendNotification("textDocument/didOpen", openParams);

        // Drain the open-triggered check (empty diagnostics for clean file).
        nextDiagsContaining("CmdDirtyCheck", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Change the file to dirty content with a type error.
        // didChange adds the URI to dirtyUris so dirtySnapshot() picks it up.
        String dirtyContent = "public class CmdDirtyCheck {\n"
                + "    public int m() { return \"not an int\"; }\n"
                + "}\n";
        String changeParams = "{\"textDocument\":{\"uri\":\"" + uri + "\",\"version\":2},"
                + "\"contentChanges\":[{\"text\":\"" + jsonEscape(dirtyContent) + "\"}]}";
        client.sendNotification("textDocument/didChange", changeParams);

        // Drain the change-triggered check so the next notification is from the command.
        nextDiagsContaining("CmdDirtyCheck", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Run openjml.checkJML on the file's OS path.
        String argsJson = "[\"\",\"\",\"\",\"\",\"" + jsonEscape(f.getAbsolutePath()) + "\"]";
        sendCommand(OpenJMLCommands.CHECK_JML, argsJson);

        // The command snapshots the dirty in-memory content, applies a 300 ms debounce,
        // then runs runCheckDirWithContext which writes the dirty content to a temp dir
        // and checks it instead of the clean disk file.
        JsonObject note = nextDiagsContaining("CmdDirtyCheck", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after openjml.checkJML on dirty file", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected diagnostics from dirty editor content, not clean disk file",
                diags.isEmpty());
        assertTrue("Expected Error-severity diagnostic from dirty content", hasError(diags));
    }

    // -----------------------------------------------------------------------
    // openjml.runRac — single-file wiring smoke test
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runRac ["", filePath]} must reach
     * {@link org.openjml.lsp.OpenJMLTextDocumentService#scheduleRacForPaths}
     * and publish diagnostics for the file.  A clean file produces an empty
     * (or absent) diagnostics list; the important thing is the command is
     * dispatched and does not throw.
     */
    @Test
    public void testRunRacCommandDispatch() throws Exception {
        File f = writeJava("CmdRacClean.java",
                "public class CmdRacClean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");

        // args[0] = projectId (empty = global), args[1] = source file
        String argsJson = "[\"\",\"" + jsonEscape(f.getAbsolutePath()) + "\"]";
        sendCommand(OpenJMLCommands.RUN_RAC, argsJson);

        // scheduleRacForPaths publishes diagnostics for every processed file.
        // For a clean file the list is empty; assert no errors appear.
        JsonObject note = nextDiagsContaining("CmdRacClean", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics for CmdRacClean.java", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected no Error diagnostics for valid Java", hasError(diags));
    }

    // -----------------------------------------------------------------------
    // openjml.runRac — multi-file protocol test
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runRac} with multiple source paths compiles all of them
     * in a single {@code --rac --dirs} invocation.
     *
     * <p>Two files are submitted: one valid and one with a type error.
     * The server must publish {@code textDocument/publishDiagnostics} for each
     * file.  The file with the type error must carry at least one
     * Error-severity diagnostic; the clean file must carry none.
     */
    @Test
    public void testRunRacCommandMultiFile() throws Exception {
        File good = writeJava("RacMultiGood.java",
                "public class RacMultiGood {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        File bad = writeJava("RacMultiBad.java",
                "public class RacMultiBad {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n");

        // args[0] = projectId (empty = global), args[1..2] = source files
        String argsJson = "[\"\",\""
                + jsonEscape(good.getAbsolutePath()) + "\",\""
                + jsonEscape(bad.getAbsolutePath()) + "\"]";
        sendCommand(OpenJMLCommands.RUN_RAC, argsJson);

        // Collect diagnostics for both files; order is not guaranteed.
        JsonObject goodNote = null, badNote = null;
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS);
        while ((goodNote == null || badNote == null) && System.nanoTime() < deadline) {
            long remaining = deadline - System.nanoTime();
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            String uri = msg.getAsJsonObject("params").get("uri").getAsString();
            if (uri.contains("RacMultiGood")) goodNote = msg;
            else if (uri.contains("RacMultiBad"))  badNote  = msg;
        }

        assertNotNull("Expected publishDiagnostics for RacMultiGood.java", goodNote);
        assertNotNull("Expected publishDiagnostics for RacMultiBad.java",  badNote);

        JsonArray goodDiags = goodNote.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected no Error diagnostics for valid file", hasError(goodDiags));

        JsonArray badDiags = badNote.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("Expected Error-severity diagnostic for type error in RacMultiBad.java",
                hasError(badDiags));
    }
}
