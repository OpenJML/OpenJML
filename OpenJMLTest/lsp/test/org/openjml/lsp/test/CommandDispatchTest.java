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

        JsonObject note = nextDiagsContaining("CmdEscFail", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics for CmdEscFail.java", note);
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

        // Open the file with dirty content that has a type error.
        // The server stores this as the in-memory (lastContent) version.
        String dirtyContent = "public class CmdDirtyCheck {\n"
                + "    public int m() { return \"not an int\"; }\n"
                + "}\n";
        String openParams = "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(dirtyContent) + "\"}}";
        client.sendNotification("textDocument/didOpen", openParams);

        // The open-triggered check reads from disk (clean file) and publishes empty
        // diagnostics.  Drain that notification before sending the command so the
        // second call to nextDiagsContaining sees only the command's result.
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
    // openjml.runRac — wiring smoke test
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runRac ["","","","", outputDir, filePath]} must reach
     * {@link org.openjml.lsp.OpenJMLTextDocumentService#scheduleRacForPaths},
     * compile the file with {@code --rac}, and produce a {@code .class} file in
     * the output directory.  The {@code outputDir} at arg position 4 is the
     * only command-encoding detail specific to RAC.
     */
    @Test
    public void testRunRacCommandDispatch() throws Exception {
        File f = writeJava("CmdRacClean.java",
                "public class CmdRacClean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        Path outDir = tmp.newFolder("rac-cmd-out").toPath();

        // args: ["","","","", outputDir, filePath]
        String argsJson = "[\"\",\"\",\"\",\"\",\""
                + jsonEscape(outDir.toString()) + "\",\""
                + jsonEscape(f.getAbsolutePath()) + "\"]";
        sendCommand(OpenJMLCommands.RUN_RAC, argsJson);

        // RAC runs async; poll for the class file.
        Path classFile = outDir.resolve("CmdRacClean.class");
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS);
        while (!Files.exists(classFile) && System.nanoTime() < deadline) {
            Thread.sleep(500);
        }
        assertTrue("Expected CmdRacClean.class in RAC output directory",
                Files.exists(classFile));
    }
}
