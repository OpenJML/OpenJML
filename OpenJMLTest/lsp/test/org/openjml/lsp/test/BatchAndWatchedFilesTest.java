package org.openjml.lsp.test;

import com.google.gson.JsonArray;
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
 * Protocol-layer tests for batch commands ({@code openjml.checkJML},
 * {@code openjml.runRac}) and {@code workspace/didChangeWatchedFiles} routing.
 *
 * <p>A single in-process LSP server is shared across all tests via
 * {@code @BeforeClass} / {@code @AfterClass}.  Each test uses a distinct
 * source file (unique class name) so {@link #nextDiagsFor(String, long, TimeUnit)}
 * can select the right notification without cross-test interference.
 *
 * <h3>Coverage targets</h3>
 * <ul>
 *   <li>{@link #testCheckJmlSingleFileNoDiags} — {@code openjml.checkJML} on a
 *       clean file invokes {@code scheduleCheckForPaths} and publishes empty
 *       diagnostics.</li>
 *   <li>{@link #testCheckJmlWithTypeError} — {@code openjml.checkJML} on a file
 *       with a type error publishes at least one error diagnostic.</li>
 *   <li>{@link #testRunRacCleanFile} — {@code openjml.runRac} on a clean file
 *       invokes {@code scheduleRacForPaths} and publishes empty diagnostics.</li>
 *   <li>{@link #testWatchedJavaDeletedPublishesEmptyDiags} — a DELETED
 *       {@code workspace/didChangeWatchedFiles} event for a {@code .java} file
 *       not open in the editor exercises {@code handleWatchedJavaChange} and
 *       publishes an empty-diagnostics clear.</li>
 *   <li>{@link #testWatchedJmlChangedRechecksCompanion} — a CHANGED event for a
 *       {@code .jml} file on disk exercises {@code handleWatchedJmlChange}: the
 *       companion {@code .java} is read from disk, checked, and its diagnostics
 *       are published.</li>
 * </ul>
 *
 * <h3>Command argument format</h3>
 * All batch commands use the old VS Code 4-element prefix format:
 * {@code ["sourcePath", "classPath", "specsPath", "propertiesFile", path1, ...]}.
 * The four prefix elements are passed as empty strings; actual paths start at
 * position 4.  For {@code openjml.runRac} the output directory is at position 4
 * and the source paths start at position 5.
 */
public class BatchAndWatchedFilesTest {

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
        tmpDir = Files.createTempDirectory("BatchAndWatchedFilesTest-");
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
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to initialize", resp);
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
        // Clean Java file — no type errors, no JML.
        write("BatchClean.java",
                "public class BatchClean {\n"
                + "    public int add(int a, int b) { return a + b; }\n"
                + "}\n");

        // Java file with a deliberate type error (return type mismatch).
        write("BatchTypeError.java",
                "public class BatchTypeError {\n"
                + "    public int m() { return \"not an int\"; }\n"
                + "}\n");

        // Clean Java file used for RAC compilation.
        write("BatchRac.java",
                "public class BatchRac {\n"
                + "    public void hello() { System.out.println(\"hello\"); }\n"
                + "}\n");

        // Companion .java and .jml files for the watched-.jml test.
        // resolveCompanionJavaUri() strategy 1: same-name replacement (Foo.jml → Foo.java),
        // checks that the .java file exists in the same directory.
        write("BatchJmlSpec.java",
                "public class BatchJmlSpec {\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n");
        write("BatchJmlSpec.jml",
                "public class BatchJmlSpec {\n"
                + "    //@ requires true;\n"
                + "    public int m(int x);\n"
                + "}\n");
    }

    private static void write(String name, String content) throws Exception {
        Files.writeString(tmpDir.resolve(name), content, StandardCharsets.UTF_8);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Absolute OS path of the named file in {@code tmpDir}. */
    private static String absPath(String name) {
        return tmpDir.resolve(name).toAbsolutePath().toString();
    }

    /** {@code file://} URI of the named file in {@code tmpDir}. */
    private static String fileUri(String name) {
        return tmpDir.resolve(name).toAbsolutePath().toUri().toString();
    }

    /**
     * Wait for the next {@code textDocument/publishDiagnostics} whose URI
     * contains {@code fragment}.
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

    /**
     * Send an {@code openjml.checkJML} or similar batch command using the old
     * VS Code 4-element-prefix format and drain the immediate null response.
     *
     * <p>Format: {@code ["", "", "", "", path1, path2, ...]} where the first four
     * empty strings are the {@code sourcePath / classPath / specsPath /
     * propertiesFile} sentinels.
     */
    private static void sendBatchCommand(String command, String... osPaths) throws Exception {
        StringBuilder sb = new StringBuilder("[\"\",\"\",\"\",\"\"");
        for (String p : osPaths) {
            sb.append(",\"").append(p.replace("\\", "\\\\")).append("\"");
        }
        sb.append("]");
        String params = "{\"command\":\"" + command + "\",\"arguments\":" + sb + "}";
        client.sendRequest("workspace/executeCommand", params);
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    // -----------------------------------------------------------------------
    // openjml.checkJML — clean file
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.checkJML} on a clean Java file must publish empty diagnostics.
     *
     * <p>Exercises {@code scheduleCheckForPaths} → {@code runCheckDirWithContext}
     * → stale-diag-clear branch (no diagnostics for the clean file).
     */
    @Test
    public void testCheckJmlSingleFileNoDiags() throws Exception {
        sendBatchCommand(OpenJMLCommands.CHECK_JML, absPath("BatchClean.java"));

        JsonObject note = nextDiagsFor("BatchClean", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after openjml.checkJML on clean file", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("Clean Java file must produce empty diagnostics", diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // openjml.checkJML — file with a type error
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.checkJML} on a file with a type error must publish at least
     * one error-severity diagnostic.
     *
     * <p>Exercises the {@code diagnosticsByUri} non-empty branch of
     * {@code scheduleCheckForPaths}.
     */
    @Test
    public void testCheckJmlWithTypeError() throws Exception {
        sendBatchCommand(OpenJMLCommands.CHECK_JML, absPath("BatchTypeError.java"));

        JsonObject note = nextDiagsFor("BatchTypeError", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after openjml.checkJML on erroneous file",
                note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("File with type error must produce at least one diagnostic", diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // openjml.runRac — clean file
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runRac} on a clean Java file must succeed (exit 0) and
     * publish empty diagnostics.
     *
     * <p>The old VS Code format for {@code openjml.runRac} is:
     * {@code ["", "", "", "", outputDir, path1, ...]} where {@code outputDir} is
     * at position 4 and source paths start at position 5.
     *
     * <p>Exercises {@code scheduleRacForPaths} → {@code CheckRunner.runRacPaths}.
     */
    @Test
    public void testRunRacCleanFile() throws Exception {
        Path racOut = tmpDir.resolve("rac-out");
        Files.createDirectories(racOut);

        // RUN_RAC old format: args[4] = outputDir, args[5+] = source paths.
        String racOutEscaped  = racOut.toAbsolutePath().toString().replace("\\", "\\\\");
        String racPathEscaped = absPath("BatchRac.java").replace("\\", "\\\\");
        String params = "{\"command\":\"" + OpenJMLCommands.RUN_RAC
                + "\",\"arguments\":[\"\",\"\",\"\",\"\",\""
                + racOutEscaped + "\",\"" + racPathEscaped + "\"]}";
        client.sendRequest("workspace/executeCommand", params);
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        JsonObject note = nextDiagsFor("BatchRac", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after openjml.runRac", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("RAC compile of clean file must produce empty diagnostics", diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // workspace/didChangeWatchedFiles — DELETED (.java)
    // -----------------------------------------------------------------------

    /**
     * A {@code workspace/didChangeWatchedFiles} DELETED event for a {@code .java}
     * file that is not open in the editor must publish empty diagnostics for that
     * URI, clearing any stale markers.
     *
     * <p>Exercises {@code handleWatchedJavaChange} DELETED branch:
     * {@code CheckRunner.getASTCache().remove(uri)} and
     * {@code client.publishDiagnostics(..., emptyList())}.
     *
     * <p>The sentinel URI {@code file:///BatchDeletedSentinel.java} is never
     * opened in the editor (not in {@code lastContent}), so the handler does not
     * short-circuit.  No real file on disk is required for DELETED.
     * Because no workspace roots are configured, {@code isUnderEffectiveRoot}
     * returns {@code true} for any URI.
     *
     * <p>LSP FileChangeType values: 1=Created, 2=Changed, 3=Deleted.
     */
    @Test
    public void testWatchedJavaDeletedPublishesEmptyDiags() throws Exception {
        String uri = "file:///BatchDeletedSentinel.java";
        String watchedParams = "{\"changes\":[{\"uri\":\"" + uri + "\",\"type\":3}]}";
        client.sendNotification("workspace/didChangeWatchedFiles", watchedParams);

        JsonObject note = nextDiagsFor("BatchDeletedSentinel", SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("DELETED event must publish empty diagnostics for the URI", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("DELETED event must publish empty diagnostics (to clear stale markers)",
                diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // workspace/didChangeWatchedFiles — CHANGED (.jml)
    // -----------------------------------------------------------------------

    /**
     * A CHANGED event for a {@code .jml} file on disk must trigger a {@code --check}
     * of its companion {@code .java} and publish that file's diagnostics.
     *
     * <p>Exercises {@code handleWatchedJmlChange} CHANGED branch:
     * <ol>
     *   <li>Reads {@code BatchJmlSpec.jml} content from disk.</li>
     *   <li>Calls {@code resolveCompanionJavaUri} — strategy 1 (same-name
     *       substitution) finds {@code BatchJmlSpec.java} in the same directory.</li>
     *   <li>Reads {@code BatchJmlSpec.java} from disk (not in {@code lastContent}).</li>
     *   <li>Calls {@code scheduleCheckNow(javaUri, javaContent)}, which runs
     *       {@code --check} and publishes the result.</li>
     * </ol>
     *
     * <p>Both {@code BatchJmlSpec.java} and {@code BatchJmlSpec.jml} exist in
     * {@code tmpDir}.  The companion {@code .java} is clean, so empty diagnostics
     * are expected.
     */
    @Test
    public void testWatchedJmlChangedRechecksCompanion() throws Exception {
        String jmlUri = fileUri("BatchJmlSpec.jml");
        // type 2 = Changed
        String watchedParams = "{\"changes\":[{\"uri\":\"" + jmlUri + "\",\"type\":2}]}";
        client.sendNotification("workspace/didChangeWatchedFiles", watchedParams);

        // Diagnostics are published for the companion .java URI, not the .jml URI.
        // Use "BatchJmlSpec.java" as the fragment to distinguish it from "BatchJmlSpec.jml".
        JsonObject note = nextDiagsFor("BatchJmlSpec.java", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("CHANGED .jml event must trigger a --check of the companion .java "
                + "and publish diagnostics", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("Clean companion .java must produce empty diagnostics", diags.isEmpty());
    }
}
