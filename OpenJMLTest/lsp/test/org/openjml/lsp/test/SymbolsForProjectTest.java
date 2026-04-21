package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.OpenJMLCommands;
import org.openjml.lsp.OpenJMLLanguageServer;

import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for {@code openjml.symbolsForProject}.
 *
 * <p>Verifies that after a project-wide index, the command returns the correct
 * {@code SymbolInformation} objects — including the symbol name, kind, and a
 * location pointing to the right file.  Also covers the live-tier fallback path
 * (declarations in the live index are found even when no nav section has been
 * indexed for the project ID yet, e.g. after a server restart).
 *
 * <p>Two source files are used:
 * <ul>
 *   <li>{@code Alpha.java} — declares class {@code Alpha} with method {@code compute}</li>
 *   <li>{@code Beta.java} — declares class {@code Beta}</li>
 *   <li>{@code Marker.java} — has a type error, used as indexProject sync marker</li>
 * </ul>
 */
public class SymbolsForProjectTest {

    private static final long TIMEOUT_SECONDS = 120;
    private static final long SHORT_TIMEOUT   = 5;

    /** Named project ID — not {@code __workspace__} — to exercise the per-project path. */
    private static final String PROJECT_ID = "TestProject";

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    private OpenJMLLanguageServer server;
    private RawLspClient          client;
    private Path                  tmpDir;

    @Before
    public void setUp() throws Exception {
        tmpDir = tmp.getRoot().toPath();

        Files.writeString(tmpDir.resolve("Alpha.java"),
                "public class Alpha {\n"
                + "    public int compute(int x) { return x + 1; }\n"
                + "}\n",
                StandardCharsets.UTF_8);

        Files.writeString(tmpDir.resolve("Beta.java"),
                "public class Beta {\n"
                + "    public void run() {}\n"
                + "}\n",
                StandardCharsets.UTF_8);

        // Marker.java has a type error to act as an indexProject completion signal.
        Files.writeString(tmpDir.resolve("Marker.java"),
                "public class Marker {\n"
                + "    public int m() { return \"type error\"; }\n"
                + "}\n",
                StandardCharsets.UTF_8);

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

    @After
    public void tearDown() {
        if (client != null) client.stop();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static String escape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"");
    }

    /** Configure the server with a named project whose root is {@code tmpDir}. */
    private void configureNamedProject() throws Exception {
        String root = escape(tmpDir.toAbsolutePath().toString());
        String settings = "{\"openjml\":{\"projects\":[{\"id\":\"" + PROJECT_ID
                + "\",\"rootPaths\":[\"" + root + "\"]}]}}";
        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":" + settings + "}");
        Thread.sleep(100);
    }

    /** Send {@code openjml.indexProject} for {@code PROJECT_ID} and wait for the sync marker. */
    private void indexProject() throws Exception {
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.INDEX_PROJECT
                + "\",\"arguments\":[\"" + PROJECT_ID + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Marker.java has a type error; its diagnostic confirms indexProject completed.
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS);
        while (true) {
            long rem = deadline - System.nanoTime();
            assertTrue("indexProject must complete within timeout", rem > 0);
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", rem, TimeUnit.NANOSECONDS);
            assertNotNull("indexProject must publish diagnostics", msg);
            JsonObject params = msg.getAsJsonObject("params");
            if (!params.get("uri").getAsString().contains("Marker")) continue;
            if (!params.getAsJsonArray("diagnostics").isEmpty()) break;
        }
    }

    /**
     * Send {@code openjml.symbolsForProject} and return the result array.
     * Asserts that the response has a {@code result} field that is a JSON array.
     */
    private JsonArray querySymbols(String query, String projectId) throws Exception {
        String pidJson = projectId == null ? "null" : "\"" + escape(projectId) + "\"";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.SYMBOLS_FOR_PROJECT
                + "\",\"arguments\":[\"" + escape(query) + "\"," + pidJson + "]}");
        JsonObject resp = client.nextResponse(TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Server must respond to symbolsForProject", resp);
        assertFalse("symbolsForProject must not return an error", resp.has("error"));
        assertTrue("symbolsForProject result must be present", resp.has("result"));
        JsonElement resultEl = resp.get("result");
        assertTrue("symbolsForProject result must be a JSON array",
                resultEl.isJsonArray());
        return resultEl.getAsJsonArray();
    }

    /** Find a symbol in the result array by name and kind (LSP SymbolKind integer). */
    private static JsonObject findSymbol(JsonArray arr, String name, int kind) {
        for (JsonElement el : arr) {
            JsonObject obj = el.getAsJsonObject();
            JsonElement nameEl = obj.get("name");
            JsonElement kindEl = obj.get("kind");
            if (nameEl != null && name.equals(nameEl.getAsString())
                    && kindEl != null && kindEl.getAsInt() == kind) {
                return obj;
            }
        }
        return null;
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /**
     * After {@code openjml.indexProject}, {@code openjml.symbolsForProject} with
     * an exact class name must return a {@code SymbolInformation} for that class
     * whose location URI ends in the correct file name.
     */
    @Test
    public void testSymbolsForProject_classFound() throws Exception {
        configureNamedProject();
        indexProject();

        // SymbolKind.Class = 5
        JsonArray results = querySymbols("Alpha", PROJECT_ID);
        assertFalse("symbolsForProject('Alpha') must return at least one result",
                results.isEmpty());

        JsonObject alphaSym = findSymbol(results, "Alpha", 5);
        assertNotNull("Result must contain 'Alpha' with SymbolKind.Class (5)", alphaSym);

        JsonObject location = alphaSym.getAsJsonObject("location");
        assertNotNull("Alpha symbol must have a location", location);
        String uri = location.get("uri").getAsString();
        assertTrue("Alpha symbol location must point to Alpha.java; got: " + uri,
                uri.endsWith("Alpha.java") || uri.contains("Alpha.java"));

        JsonObject range = location.getAsJsonObject("range");
        assertNotNull("Alpha symbol location must have a range", range);
        // The range must not be zero-width (start != end character).
        JsonObject start = range.getAsJsonObject("start");
        JsonObject end   = range.getAsJsonObject("end");
        int startChar = start.get("character").getAsInt();
        int endChar   = end.get("character").getAsInt();
        assertTrue("Alpha symbol range must not be zero-width (start=" + startChar
                + " end=" + endChar + ")", endChar > startChar);
    }

    /**
     * {@code openjml.symbolsForProject} with an empty query must return all
     * non-synthetic declarations from both source files in the project.
     */
    @Test
    public void testSymbolsForProject_emptyQueryReturnsAll() throws Exception {
        configureNamedProject();
        indexProject();

        JsonArray results = querySymbols("", PROJECT_ID);
        assertFalse("Empty query must return at least one result", results.isEmpty());

        // Both classes must be present.
        assertNotNull("Alpha class must appear in full-project results",
                findSymbol(results, "Alpha", 5));
        assertNotNull("Beta class must appear in full-project results",
                findSymbol(results, "Beta", 5));

        // The method from Alpha must also be present.
        // SymbolKind.Method = 6
        assertNotNull("Alpha.compute() must appear in full-project results",
                findSymbol(results, "compute", 6));
    }

    /**
     * A query that does not match any symbol must return an empty array,
     * not an error.
     */
    @Test
    public void testSymbolsForProject_noMatch() throws Exception {
        configureNamedProject();
        indexProject();

        JsonArray results = querySymbols("xyzzy_no_such_symbol_99999", PROJECT_ID);
        assertEquals("Query matching nothing must return empty array", 0, results.size());
    }

    /**
     * Querying with a null project ID must search all projects (same as
     * {@code workspace/symbol} with no filter) and still return results.
     */
    @Test
    public void testSymbolsForProject_nullProjectIdSearchesAll() throws Exception {
        configureNamedProject();
        indexProject();

        JsonArray results = querySymbols("Alpha", null);
        assertFalse("Null projectId must search all projects and still return Alpha",
                results.isEmpty());
        assertNotNull("Alpha class must be found with null projectId",
                findSymbol(results, "Alpha", 5));
    }

    /**
     * Querying with a projectId that is not registered must produce an error
     * notification and return an empty array (not throw an exception).
     */
    @Test
    public void testSymbolsForProject_unknownProjectIdReturnsEmpty() throws Exception {
        configureNamedProject();
        // No indexProject — just configure and query with a bad ID.
        JsonArray results = querySymbols("Alpha", "NonExistentProject");
        assertEquals("Unknown project ID must return empty array", 0, results.size());
    }

    /**
     * Even without a prior {@code openjml.indexProject}, a file that was opened
     * (and thus populated the live declaration index) must be found by
     * {@code openjml.symbolsForProject}.
     *
     * <p>This exercises the live-tier fallback path in
     * {@link org.openjml.lsp.ASTCache#forEachDeclarationForProject}: when no nav
     * section exists for the project ID yet, configured roots from the project
     * settings are used to filter live-index entries.
     */
    @Test
    public void testSymbolsForProject_liveIndexFallback() throws Exception {
        configureNamedProject();
        // Open Alpha.java to populate the live declaration index (triggers a --check).
        String alphaContent = Files.readString(tmpDir.resolve("Alpha.java"),
                StandardCharsets.UTF_8);
        String alphaUri = tmpDir.resolve("Alpha.java").toUri().toString();
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + escape(alphaUri)
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + alphaContent.replace("\\", "\\\\")
                                              .replace("\"", "\\\"")
                                              .replace("\n", "\\n") + "\"}}");

        // Wait for the check to complete (diagnostics published for Alpha.java).
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS);
        while (true) {
            long rem = deadline - System.nanoTime();
            assertTrue("didOpen check must complete within timeout", rem > 0);
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", rem, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            if (msg.getAsJsonObject("params").get("uri").getAsString().contains("Alpha")) break;
        }

        // symbolsForProject must find Alpha via the live index fallback (no navSection yet).
        JsonArray results = querySymbols("Alpha", PROJECT_ID);
        assertFalse("symbolsForProject must find Alpha via live index fallback",
                results.isEmpty());
        assertNotNull("Alpha class must be found via live index",
                findSymbol(results, "Alpha", 5));
    }
}
