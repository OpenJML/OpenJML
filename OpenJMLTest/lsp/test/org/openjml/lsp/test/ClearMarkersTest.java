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
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for the two marker-clearing commands:
 *
 * <ul>
 *   <li>{@code openjml.clearMarkers} — clears all diagnostics in the workspace.</li>
 *   <li>{@code openjml.clearMarkersForUris} — clears diagnostics for specific
 *       file URIs only, leaving other files untouched.</li>
 * </ul>
 *
 * <p>Each test establishes real CHECK diagnostics via {@code openjml.checkJML},
 * then invokes the clear command and verifies the published results.  This
 * distinguishes the two commands: {@code clearMarkers} must clear all files,
 * while {@code clearMarkersForUris} must clear only the targeted file and leave
 * the other file's diagnostics intact.
 */
public class ClearMarkersTest extends ProtocolTestBase {

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

    private File writeJava(String name, String content) throws Exception {
        File f = tmp.newFile(name);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    /** Source with a guaranteed type error (return type mismatch). */
    private static String errSrc(String className) {
        return "public class " + className + " {\n"
                + "    public int m() { return \"not an int\"; }\n"
                + "}\n";
    }

    /** Run openjml.checkJML on {@code path} and wait for diagnostics for {@code nameFragment}. */
    private JsonArray checkAndGetDiags(String path, String nameFragment) throws Exception {
        String argsJson = "[\"\",\"\",\"\",\"\",\"" + jsonEscape(path) + "\"]";
        executeCommand(OpenJMLCommands.CHECK_JML, argsJson);
        JsonObject note = nextDiagsFor(nameFragment, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics for " + nameFragment, note);
        return note.getAsJsonObject("params").getAsJsonArray("diagnostics");
    }

    /** Drain all publishDiagnostics notifications that arrive within {@code timeoutMs}. */
    private void drainDiags(long timeoutMs) throws InterruptedException {
        long deadline = System.nanoTime() + timeoutMs * 1_000_000L;
        while (System.nanoTime() < deadline) {
            long rem = deadline - System.nanoTime();
            if (client.nextNotification("textDocument/publishDiagnostics",
                    rem, TimeUnit.NANOSECONDS) == null) break;
        }
    }

    private static boolean hasCheckError(JsonArray diags) {
        return hasErrorDiagWithSource(diags, DiagnosticConverter.SOURCE_CHECK);
    }

    // -----------------------------------------------------------------------
    // openjml.clearMarkers — clears ALL files
    // -----------------------------------------------------------------------

    /**
     * After CHECK diagnostics are established for two files, {@code clearMarkers}
     * must publish empty diagnostics for both.
     */
    @Test
    public void testClearMarkersAll() throws Exception {
        File fA = writeJava("ClearAllA.java", errSrc("ClearAllA"));
        File fB = writeJava("ClearAllB.java", errSrc("ClearAllB"));
        String uriA = fA.toPath().toUri().toString();
        String uriB = fB.toPath().toUri().toString();

        // Establish errors on both files.
        JsonArray diagsA = checkAndGetDiags(fA.getAbsolutePath(), "ClearAllA");
        assertTrue("ClearAllA must have a CHECK error before clear", hasCheckError(diagsA));
        JsonArray diagsB = checkAndGetDiags(fB.getAbsolutePath(), "ClearAllB");
        assertTrue("ClearAllB must have a CHECK error before clear", hasCheckError(diagsB));

        // Send clearMarkers (no arguments).
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.CLEAR_MARKERS + "\",\"arguments\":[]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Both files must receive empty publishDiagnostics.
        boolean clearedA = false, clearedB = false;
        long deadline = System.nanoTime() + SHORT_TIMEOUT * 1_000_000_000L;
        while (!(clearedA && clearedB) && System.nanoTime() < deadline) {
            long rem = deadline - System.nanoTime();
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", rem, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            String uri = params.get("uri").getAsString();
            JsonArray diags = params.getAsJsonArray("diagnostics");
            if (diags.isEmpty()) {
                if (uri.equals(uriA)) clearedA = true;
                if (uri.equals(uriB)) clearedB = true;
            }
        }
        assertTrue("clearMarkers must publish empty diags for ClearAllA", clearedA);
        assertTrue("clearMarkers must publish empty diags for ClearAllB", clearedB);
    }

    // -----------------------------------------------------------------------
    // openjml.clearMarkersForUris — clears only the targeted file
    // -----------------------------------------------------------------------

    /**
     * After CHECK diagnostics are established for two files, {@code clearMarkersForUris}
     * targeting only file A must:
     * <ul>
     *   <li>publish empty diagnostics for A, and</li>
     *   <li>NOT publish empty diagnostics for B (B's diagnostics remain).</li>
     * </ul>
     *
     * <p>This test distinguishes {@code clearMarkersForUris} from {@code clearMarkers}:
     * if the wrong command ({@code clearMarkers}) were dispatched, B would also be cleared.
     */
    @Test
    public void testClearMarkersForUrisTargetsOnlySelectedFile() throws Exception {
        File fA = writeJava("ClearSelA.java", errSrc("ClearSelA"));
        File fB = writeJava("ClearSelB.java", errSrc("ClearSelB"));
        String uriA = fA.toPath().toUri().toString();
        String uriB = fB.toPath().toUri().toString();

        // Establish errors on both files.
        JsonArray diagsA = checkAndGetDiags(fA.getAbsolutePath(), "ClearSelA");
        assertTrue("ClearSelA must have a CHECK error before clear", hasCheckError(diagsA));
        JsonArray diagsB = checkAndGetDiags(fB.getAbsolutePath(), "ClearSelB");
        assertTrue("ClearSelB must have a CHECK error before clear", hasCheckError(diagsB));

        // Send clearMarkersForUris targeting only file A.
        // args[0] = projectId (null = all projects), args[1+] = file URIs.
        String argsJson = "[null,\"" + jsonEscape(uriA) + "\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.CLEAR_MARKERS_FOR_URIS
                + "\",\"arguments\":" + argsJson + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Collect all publishDiagnostics notifications for 3 seconds.
        boolean clearedA = false, clearedB = false;
        long deadline = System.nanoTime() + 3_000_000_000L;
        while (System.nanoTime() < deadline) {
            long rem = deadline - System.nanoTime();
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", rem, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            String uri = params.get("uri").getAsString();
            JsonArray diags = params.getAsJsonArray("diagnostics");
            if (uri.equals(uriA) && diags.isEmpty()) clearedA = true;
            if (uri.equals(uriB) && diags.isEmpty()) clearedB = true;
        }

        assertTrue("clearMarkersForUris must publish empty diags for targeted file A", clearedA);
        assertFalse("clearMarkersForUris must NOT clear non-targeted file B", clearedB);
    }

    // -----------------------------------------------------------------------
    // openjml.clearMarkersForUris — orphan: publish empty even when not tracked
    // -----------------------------------------------------------------------

    /**
     * {@code clearMarkersForUris} must publish empty diagnostics for a targeted
     * file URI even when the server has no record of that URI in its internal
     * {@code markedUris} tracking set.
     *
     * <p>This reproduces the orphan-diagnostic scenario: a diagnostic was
     * published but the server's tracking was subsequently cleared (e.g., by a
     * race or server restart), leaving a stale marker visible in the client.
     * The clear command must still send an empty publication to remove it.
     */
    @Test
    public void testClearMarkersForUrisPublishesEmptyForUntrackedUri() throws Exception {
        File fA = writeJava("ClearOrphan.java", errSrc("ClearOrphan"));
        String uriA = fA.toPath().toUri().toString();

        // Establish an error, then call clearMarkers (all) to wipe server tracking.
        JsonArray diags = checkAndGetDiags(fA.getAbsolutePath(), "ClearOrphan");
        assertTrue("ClearOrphan must have a CHECK error", hasCheckError(diags));

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.CLEAR_MARKERS + "\",\"arguments\":[]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        drainDiags(2_000);  // absorb the empty publication from clearMarkers

        // Now the server's markedUris is empty, but the client may still show the marker.
        // Send clearMarkersForUris for the same URI — the server must still publish empty.
        String argsJson = "[null,\"" + jsonEscape(uriA) + "\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.CLEAR_MARKERS_FOR_URIS
                + "\",\"arguments\":" + argsJson + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        boolean clearedA = false;
        long deadline = System.nanoTime() + 3_000_000_000L;
        while (System.nanoTime() < deadline) {
            long rem = deadline - System.nanoTime();
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", rem, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            if (params.get("uri").getAsString().equals(uriA)
                    && params.getAsJsonArray("diagnostics").isEmpty()) {
                clearedA = true;
                break;
            }
        }
        assertTrue("clearMarkersForUris must publish empty for untracked URI", clearedA);
    }
}
