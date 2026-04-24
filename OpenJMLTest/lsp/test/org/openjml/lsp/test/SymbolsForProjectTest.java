package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.OpenJMLCommands;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for {@code openjml.symbolsForProject} and
 * {@code workspace/symbol}.
 *
 * <p>Single-project tests verify that after a project-wide index the command
 * returns correct {@code WorkspaceSymbol} objects.  Multi-project tests verify
 * that:
 * <ul>
 *   <li>{@code workspace/symbol} with an encoded project ID and
 *       {@code openjml.symbolsForProject} return identical results for the same
 *       project.</li>
 *   <li>All three APIs ({@code workspace/symbol} scoped, {@code symbolsForProject},
 *       and {@code workspace/symbol} unscoped) return results in the same
 *       {@code WorkspaceSymbol} format (name, kind, location with uri+range).</li>
 *   <li>The unscoped {@code workspace/symbol} result is a superset of the scoped
 *       results when multiple projects are indexed.</li>
 *   <li>Specific symbol names, kinds (LSP {@code SymbolKind} integers), and file
 *       URIs are correct.</li>
 * </ul>
 */
public class SymbolsForProjectTest extends ProtocolTestBase {

    /** Named project ID — not {@code __workspace__} — to exercise the per-project path. */
    private static final String PROJECT_ID = "TestProject";

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    private Path tmpDir;

    @Before
    @Override
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

        startServer();
    }

    @After
    @Override
    public void tearDown() {
        super.tearDown();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Configure the server with a named project whose root is {@code tmpDir}. */
    private void configureNamedProject() throws Exception {
        String root = jsonEscape(tmpDir.toAbsolutePath().toString());
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
        String pidJson = projectId == null ? "null" : "\"" + jsonEscape(projectId) + "\"";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.SYMBOLS_FOR_PROJECT
                + "\",\"arguments\":[\"" + jsonEscape(query) + "\"," + pidJson + "]}");
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
     * Send {@code workspace/symbol} with the given query and return the result array.
     * The query may contain a newline to encode a project ID:
     * {@code "<projectId>\nidentifier"}.
     */
    private JsonArray queryWorkspaceSymbol(String query) throws Exception {
        String jsonQuery = query
                .replace("\\", "\\\\")
                .replace("\"", "\\\"")
                .replace("\n", "\\n")
                .replace("\r", "\\r")
                .replace("\t", "\\t");
        client.sendRequest("workspace/symbol", "{\"query\":\"" + jsonQuery + "\"}");
        JsonObject resp = client.nextResponse(TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Server must respond to workspace/symbol", resp);
        assertFalse("workspace/symbol must not return an error", resp.has("error"));
        assertTrue("workspace/symbol result must be present", resp.has("result"));
        JsonElement resultEl = resp.get("result");
        assertTrue("workspace/symbol result must be a JSON array", resultEl.isJsonArray());
        return resultEl.getAsJsonArray();
    }

    /** Configure two named projects with separate root directories. */
    private void configureMultiProject(String alphaRoot, String betaRoot) throws Exception {
        String rootA = jsonEscape(alphaRoot);
        String rootB = jsonEscape(betaRoot);
        String settings = "{\"openjml\":{\"projects\":["
                + "{\"id\":\"ProjectAlpha\",\"rootPaths\":[\"" + rootA + "\"]},"
                + "{\"id\":\"ProjectBeta\",\"rootPaths\":[\"" + rootB + "\"]}"
                + "]}}";
        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":" + settings + "}");
        Thread.sleep(100);
    }

    /** Index a named project and wait for the marker file to publish diagnostics. */
    private void indexNamedProject(String projectId, String markerFileName) throws Exception {
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.INDEX_PROJECT
                + "\",\"arguments\":[\"" + projectId + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS);
        while (true) {
            long rem = deadline - System.nanoTime();
            assertTrue("indexProject " + projectId + " must complete within timeout", rem > 0);
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", rem, TimeUnit.NANOSECONDS);
            assertNotNull("indexProject " + projectId + " must publish diagnostics", msg);
            JsonObject params = msg.getAsJsonObject("params");
            if (!params.get("uri").getAsString().contains(markerFileName)) continue;
            if (!params.getAsJsonArray("diagnostics").isEmpty()) break;
        }
    }

    /**
     * Assert every element in {@code arr} is a well-formed {@code WorkspaceSymbol}:
     * has {@code name}, {@code kind}, and {@code location} with {@code uri} and
     * {@code range} (with {@code start} and {@code end}).
     */
    private static void assertWorkspaceSymbolFormat(JsonArray arr, String label) {
        assertFalse(label + " must not be empty for format check", arr.isEmpty());
        for (JsonElement el : arr) {
            assertTrue(label + ": each element must be a JSON object", el.isJsonObject());
            JsonObject obj = el.getAsJsonObject();
            assertTrue(label + ": must have 'name'",     obj.has("name"));
            assertTrue(label + ": must have 'kind'",     obj.has("kind"));
            assertTrue(label + ": must have 'location'", obj.has("location"));
            JsonObject loc = obj.getAsJsonObject("location");
            assertTrue(label + ": location must have 'uri'",   loc.has("uri"));
            assertTrue(label + ": location must have 'range'", loc.has("range"));
            JsonObject range = loc.getAsJsonObject("range");
            assertTrue(label + ": range must have 'start'", range.has("start"));
            assertTrue(label + ": range must have 'end'",   range.has("end"));
        }
    }

    /**
     * Assert that two symbol arrays contain the same set of symbols, identified
     * by the triple (name, kind, uri).
     */
    private static void assertSameSymbols(String label, JsonArray a, JsonArray b) {
        java.util.Set<String> keysA = symbolKeys(a);
        java.util.Set<String> keysB = symbolKeys(b);
        assertEquals(label, keysA, keysB);
    }

    private static java.util.Set<String> symbolKeys(JsonArray arr) {
        java.util.Set<String> keys = new java.util.LinkedHashSet<>();
        for (JsonElement el : arr) {
            JsonObject obj = el.getAsJsonObject();
            String name = obj.get("name").getAsString();
            int    kind = obj.get("kind").getAsInt();
            String uri  = obj.getAsJsonObject("location").get("uri").getAsString();
            keys.add(name + ":" + kind + ":" + uri);
        }
        return keys;
    }

    // -----------------------------------------------------------------------
    // Multi-project tests
    // -----------------------------------------------------------------------

    /**
     * Two named projects, each with a {@code sharedCompute} method plus project-unique
     * class names.  Verifies:
     * <ol>
     *   <li>All three APIs return the same {@code WorkspaceSymbol} JSON format.</li>
     *   <li>{@code workspace/symbol} with {@code "ProjectAlpha\nsharedCompute"} and
     *       {@code openjml.symbolsForProject("sharedCompute","ProjectAlpha")} return
     *       identical results.</li>
     *   <li>Unscoped {@code workspace/symbol("sharedCompute")} is a superset: it
     *       contains {@code sharedCompute} from both {@code AlphaOnly.java} and
     *       {@code BetaOnly.java}.</li>
     *   <li>The scoped result points only to {@code AlphaOnly.java}, not
     *       {@code BetaOnly.java}.</li>
     *   <li>The {@code AlphaOnly} class itself (SymbolKind.Class = 5) appears in the
     *       scoped result with its location in {@code AlphaOnly.java}.</li>
     * </ol>
     */
    @Test
    public void testMultiProject_symbolConsistencyAndSuperset() throws Exception {
        Path alphaDir = tmpDir.resolve("alpha");
        Path betaDir  = tmpDir.resolve("beta");
        Files.createDirectories(alphaDir);
        Files.createDirectories(betaDir);

        Files.writeString(alphaDir.resolve("AlphaOnly.java"),
                "public class AlphaOnly {\n"
                + "    public int sharedCompute(int x) { return x + 1; }\n"
                + "}\n", StandardCharsets.UTF_8);
        Files.writeString(alphaDir.resolve("AlphaMarker.java"),
                "public class AlphaMarker {\n"
                + "    public int m() { return \"type error\"; }\n"
                + "}\n", StandardCharsets.UTF_8);

        Files.writeString(betaDir.resolve("BetaOnly.java"),
                "public class BetaOnly {\n"
                + "    public int sharedCompute(int x) { return x * 2; }\n"
                + "}\n", StandardCharsets.UTF_8);
        Files.writeString(betaDir.resolve("BetaMarker.java"),
                "public class BetaMarker {\n"
                + "    public int m() { return \"type error\"; }\n"
                + "}\n", StandardCharsets.UTF_8);

        configureMultiProject(alphaDir.toAbsolutePath().toString(),
                              betaDir.toAbsolutePath().toString());
        indexNamedProject("ProjectAlpha", "AlphaMarker");
        indexNamedProject("ProjectBeta",  "BetaMarker");

        // Query 1: workspace/symbol scoped to ProjectAlpha via encoded query.
        JsonArray wsAlpha  = queryWorkspaceSymbol("ProjectAlpha\nsharedCompute");
        // Query 2: openjml.symbolsForProject scoped to ProjectAlpha.
        JsonArray sfpAlpha = querySymbols("sharedCompute", "ProjectAlpha");
        // Query 3: workspace/symbol with no project filter.
        JsonArray wsAll    = queryWorkspaceSymbol("sharedCompute");

        // All three must use the WorkspaceSymbol format.
        assertWorkspaceSymbolFormat(wsAlpha,  "workspace/symbol(ProjectAlpha)");
        assertWorkspaceSymbolFormat(sfpAlpha, "symbolsForProject(ProjectAlpha)");
        assertWorkspaceSymbolFormat(wsAll,    "workspace/symbol(all)");

        // Queries 1 and 2 must return exactly the same symbol set.
        assertFalse("workspace/symbol(ProjectAlpha) must be non-empty",  wsAlpha.isEmpty());
        assertFalse("symbolsForProject(ProjectAlpha) must be non-empty", sfpAlpha.isEmpty());
        assertSameSymbols(
                "workspace/symbol(ProjectAlpha) and symbolsForProject(ProjectAlpha) must match",
                wsAlpha, sfpAlpha);

        // Query 3 must be a superset.
        assertTrue("workspace/symbol(all) must have at least as many results as scoped query",
                wsAll.size() >= wsAlpha.size());

        // Scoped result: sharedCompute must point to AlphaOnly.java only.
        JsonObject alphaMethod = findSymbol(wsAlpha, "sharedCompute", 6);
        assertNotNull("sharedCompute (Method=6) must appear in ProjectAlpha results", alphaMethod);
        String alphaMethodUri = alphaMethod.getAsJsonObject("location").get("uri").getAsString();
        assertTrue("sharedCompute in ProjectAlpha must point to AlphaOnly.java; got: " + alphaMethodUri,
                alphaMethodUri.contains("AlphaOnly"));
        assertFalse("sharedCompute in ProjectAlpha must NOT point to BetaOnly.java; got: " + alphaMethodUri,
                alphaMethodUri.contains("BetaOnly"));

        // Query all ProjectAlpha symbols (empty query) to check for the AlphaOnly class.
        JsonArray wsAlphaAll = queryWorkspaceSymbol("ProjectAlpha\n");
        assertWorkspaceSymbolFormat(wsAlphaAll, "workspace/symbol(ProjectAlpha, all)");
        JsonObject alphaClass = findSymbol(wsAlphaAll, "AlphaOnly", 5);
        assertNotNull("AlphaOnly (Class=5) must appear in ProjectAlpha all-symbol results", alphaClass);
        String alphaClassUri = alphaClass.getAsJsonObject("location").get("uri").getAsString();
        assertTrue("AlphaOnly class must point to AlphaOnly.java; got: " + alphaClassUri,
                alphaClassUri.contains("AlphaOnly"));

        // Unscoped result: sharedCompute must appear for both AlphaOnly and BetaOnly.
        boolean hasAlpha = false, hasBeta = false;
        for (JsonElement el : wsAll) {
            JsonObject obj = el.getAsJsonObject();
            if (!"sharedCompute".equals(obj.get("name").getAsString())) continue;
            if (obj.get("kind").getAsInt() != 6) continue;
            String uri = obj.getAsJsonObject("location").get("uri").getAsString();
            if (uri.contains("AlphaOnly")) hasAlpha = true;
            if (uri.contains("BetaOnly"))  hasBeta  = true;
        }
        assertTrue("workspace/symbol(all) must include sharedCompute from AlphaOnly", hasAlpha);
        assertTrue("workspace/symbol(all) must include sharedCompute from BetaOnly",  hasBeta);
    }

    // -----------------------------------------------------------------------
    // Live-index fallback
    // -----------------------------------------------------------------------

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
                "{\"textDocument\":{\"uri\":\"" + jsonEscape(alphaUri)
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(alphaContent) + "\"}}");

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
