package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.OpenJMLCommands;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for per-project {@code openjml.indexProject} dispatch.
 *
 * <p>When a user selects multiple projects and invokes "Index Project", the
 * Eclipse plugin sends one {@code openjml.indexProject} command per selected
 * project, each carrying the project's ID as {@code arguments[0]}.  These tests
 * verify that each per-project command is dispatched to the correct project and
 * produces its own {@code textDocument/publishDiagnostics} notification.
 *
 * <h3>Coverage targets</h3>
 * <ul>
 *   <li>{@link #testIndexTwoProjectsIndependently} — two configured projects,
 *       two separate {@code openjml.indexProject} commands (one per project ID);
 *       each must trigger a {@code --check} pass on its own root and publish
 *       diagnostics for the error file in that project.</li>
 * </ul>
 */
public class IndexProjectMultiSelectionTest extends ProtocolTestBase {

    private Path tmpDir;

    @Before
    @Override
    public void setUp() throws Exception {
        tmpDir = Files.createTempDirectory("IndexProjectMultiSelectionTest-");
        startServer();
    }

    @After
    @Override
    public void tearDown() {
        super.tearDown();
        if (tmpDir != null && Files.exists(tmpDir)) {
            try {
                Files.walk(tmpDir)
                        .sorted(Comparator.reverseOrder())
                        .forEach(p -> p.toFile().delete());
            } catch (java.io.IOException ignored) {}
        }
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private void write(String subdir, String name, String content) throws Exception {
        Path dir = tmpDir.resolve(subdir);
        Files.createDirectories(dir);
        Files.writeString(dir.resolve(name), content, StandardCharsets.UTF_8);
    }

    private String absDir(String subdir) {
        return tmpDir.resolve(subdir).toAbsolutePath().toString();
    }

    private static String jsonEscapePath(String path) {
        return path.replace("\\", "\\\\");
    }

    private void configureTwoProjects(String idA, String rootA, String idB, String rootB)
            throws Exception {
        String rA = jsonEscapePath(rootA);
        String rB = jsonEscapePath(rootB);
        String settingsJson = "{\"openjml\":{\"projects\":["
                + "{\"id\":\"" + idA + "\",\"rootPaths\":[\"" + rA + "\"]},"
                + "{\"id\":\"" + idB + "\",\"rootPaths\":[\"" + rB + "\"]}"
                + "]}}";
        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":" + settingsJson + "}");
        Thread.sleep(100);
    }

    /** Send {@code openjml.indexProject} for a single project ID and drain the response. */
    private void sendIndexProject(String projectId) throws Exception {
        String params = "{\"command\":\"" + OpenJMLCommands.INDEX_PROJECT
                + "\",\"arguments\":[\"" + projectId + "\"]}";
        client.sendRequest("workspace/executeCommand", params);
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    // -----------------------------------------------------------------------
    // Test: two independent indexProject commands, one per project
    // -----------------------------------------------------------------------

    /**
     * Simulate the Eclipse multi-selection dispatch: two projects are configured and
     * each receives its own {@code openjml.indexProject} command with its project ID.
     *
     * <p>The commands are sent sequentially — project A's diagnostics must arrive
     * before project B's command is sent — so that the server's nav-update executor
     * processes each independently rather than merging them.
     *
     * <p>Both projects contain a Java file with a type error.  Each
     * {@code textDocument/publishDiagnostics} notification must be non-empty,
     * confirming that {@code indexProject(projectId)} correctly scoped the
     * {@code --check} pass to that project's root paths only.
     */
    @Test
    public void testIndexTwoProjectsIndependently() throws Exception {
        write("ProjectA", "ErrorA.java",
                "public class ErrorA {\n"
                + "    public int m() { return \"type error in A\"; }\n"
                + "}\n");
        write("ProjectB", "ErrorB.java",
                "public class ErrorB {\n"
                + "    public int m() { return \"type error in B\"; }\n"
                + "}\n");

        configureTwoProjects("projA", absDir("ProjectA"), "projB", absDir("ProjectB"));

        // Index project A and wait for its diagnostics before sending project B's command.
        sendIndexProject("projA");
        JsonObject noteA = nextDiagsFor("ErrorA", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("indexProject(projA) must publish diagnostics for ErrorA.java", noteA);
        JsonArray diagsA = noteA.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("ErrorA.java must have type-error diagnostics", diagsA.isEmpty());

        // Index project B independently.
        sendIndexProject("projB");
        JsonObject noteB = nextDiagsFor("ErrorB", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("indexProject(projB) must publish diagnostics for ErrorB.java", noteB);
        JsonArray diagsB = noteB.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("ErrorB.java must have type-error diagnostics", diagsB.isEmpty());
    }
}
