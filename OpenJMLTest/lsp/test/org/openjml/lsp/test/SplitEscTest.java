package org.openjml.lsp.test;

import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.openjml.lsp.OpenJMLCommands;
import org.openjml.lsp.OpenJMLLanguageServer;

import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for the split-by-file and split-by-method ESC commands.
 *
 * <p>A single in-process LSP server is shared across all tests via
 * {@code @BeforeClass} / {@code @AfterClass}.  Disk files are created in a
 * temporary directory in {@code @BeforeClass}.
 *
 * <h3>Coverage targets</h3>
 * <ul>
 *   <li>{@link #testRunEscSplitByFile} — {@code openjml.runEscSplitByFile} submits
 *       one ESC task per file on the bounded ESC thread pool
 *       ({@code scheduleEscSplitByFile}) and publishes diagnostics via
 *       {@code publishMerged} when each task completes.</li>
 *   <li>{@link #testRunEscSplitByMethod} — {@code openjml.runEscSplitByMethod}
 *       discovers methods in the file (regex fallback when no AST cache entry exists),
 *       submits one ESC task per method ({@code scheduleEscSplitByMethod}), and
 *       publishes diagnostics for each method result.</li>
 * </ul>
 *
 * <h3>Command argument format</h3>
 * Both commands use the old VS Code 4-element prefix format:
 * {@code ["sourcePath", "classPath", "specsPath", "propertiesFile", path1, ...]}.
 * The four prefix elements are empty strings; actual OS paths start at position 4.
 */
public class SplitEscTest {

    private static final long TIMEOUT_SECONDS = 120;
    private static final long SHORT_TIMEOUT   = 5;

    private static OpenJMLLanguageServer server;
    private static RawLspClient          client;
    private static Path                  tmpDir;

    // -----------------------------------------------------------------------
    // Shared server and temp-file lifecycle
    // -----------------------------------------------------------------------

    @BeforeClass
    public static void startServer() throws Exception {
        tmpDir = Files.createTempDirectory("SplitEscTest-");
        createTestFiles();

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
        assertNotNull("Server must respond to initialize",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
        client.sendNotification("initialized", "{}");
    }

    @AfterClass
    public static void stopServer() throws Exception {
        if (client != null) client.stop();
        if (tmpDir != null && Files.exists(tmpDir)) {
            Files.walk(tmpDir)
                    .sorted(Comparator.reverseOrder())
                    .forEach(p -> p.toFile().delete());
        }
    }

    private static void createTestFiles() throws Exception {
        // Single-method file for split-by-file test.
        // No JML specs — ESC exits quickly with no diagnostics.
        write("SplitFile1.java",
                "public class SplitFile1 {\n"
                + "    public int add(int a, int b) { return a + b; }\n"
                + "}\n");

        // Two-method file for split-by-method test.
        // No JML specs — each method's ESC task exits quickly.
        write("SplitMethod1.java",
                "public class SplitMethod1 {\n"
                + "    public int add(int a, int b) { return a + b; }\n"
                + "    public int sub(int a, int b) { return a - b; }\n"
                + "}\n");
    }

    private static void write(String name, String content) throws Exception {
        Files.writeString(tmpDir.resolve(name), content, StandardCharsets.UTF_8);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static String absPath(String name) {
        return tmpDir.resolve(name).toAbsolutePath().toString();
    }

    private static String jsonEscapePath(String path) {
        return path.replace("\\", "\\\\");
    }

    /**
     * Send a split-ESC command using the old VS Code 4-element-prefix format and
     * drain the immediate null response.  The command argument list is:
     * {@code ["", "", "", "", path1, ...]}.
     */
    private static void sendSplitEscCommand(String command, String... osPaths)
            throws Exception {
        StringBuilder sb = new StringBuilder("[\"\",\"\",\"\",\"\"");
        for (String p : osPaths) {
            sb.append(",\"").append(jsonEscapePath(p)).append("\"");
        }
        sb.append("]");
        String params = "{\"command\":\"" + command + "\",\"arguments\":" + sb + "}";
        client.sendRequest("workspace/executeCommand", params);
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    /**
     * Wait for the next {@code textDocument/publishDiagnostics} whose URI contains
     * {@code fragment}.
     */
    private static JsonObject nextDiagsFor(String fragment, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            if (msg.getAsJsonObject("params").get("uri").getAsString().contains(fragment))
                return msg;
        }
    }

    // -----------------------------------------------------------------------
    // openjml.runEscSplitByFile — one task per file
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEscSplitByFile} on a single clean Java file must:
     * <ol>
     *   <li>Expand the path to one {@code .java} file via {@code collectJavaFiles}.</li>
     *   <li>Submit one ESC task to the bounded ESC thread pool.</li>
     *   <li>Call {@code publishMerged(uri)} when the task completes, producing a
     *       {@code textDocument/publishDiagnostics} notification.</li>
     * </ol>
     *
     * <p>The file has no JML specs so the ESC result is empty diagnostics.
     */
    @Test
    public void testRunEscSplitByFile() throws Exception {
        sendSplitEscCommand(OpenJMLCommands.RUN_ESC_SPLIT_BY_FILE,
                absPath("SplitFile1.java"));

        JsonObject note = nextDiagsFor("SplitFile1", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after runEscSplitByFile", note);
    }

    // -----------------------------------------------------------------------
    // openjml.runEscSplitByMethod — one task per method
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEscSplitByMethod} on a file with two methods must:
     * <ol>
     *   <li>Expand the path to one {@code .java} file.</li>
     *   <li>Discover two methods via regex ({@code JavaSourceScanner.findMethods}
     *       — no AST cache entry exists for an un-opened disk file).</li>
     *   <li>Submit two ESC tasks, one per method, and call {@code publishMerged(uri)}
     *       as each method finishes.</li>
     * </ol>
     *
     * <p>The file has no JML specs so all method results are empty diagnostics.
     * The test waits for at least one {@code publishDiagnostics} for the file URI,
     * confirming that the method-level dispatch executed.
     */
    @Test
    public void testRunEscSplitByMethod() throws Exception {
        sendSplitEscCommand(OpenJMLCommands.RUN_ESC_SPLIT_BY_METHOD,
                absPath("SplitMethod1.java"));

        // At least one publishDiagnostics must arrive — one per method completion.
        JsonObject note = nextDiagsFor("SplitMethod1", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after runEscSplitByMethod", note);
    }
}
