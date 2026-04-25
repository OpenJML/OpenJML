package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.After;
import org.junit.Before;
import org.openjml.lsp.DiagnosticConverter;
import org.openjml.lsp.OpenJMLLanguageServer;

import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertNotNull;

/**
 * Base class for protocol-level LSP tests.
 *
 * <p>Manages a full in-process server/client pair including the LSP initialization
 * handshake.  Each test method gets a fresh server via {@code @Before} / {@code @After}.
 *
 * <p>Subclasses that need a workspace root URI (e.g. for per-project settings lookup)
 * should override {@link #setUp()} and call {@link #startServer(String)}.
 *
 * <p>Subclasses that need extra per-test setup (temp files, etc.) should also
 * override {@link #setUp()}, perform their own setup, then call
 * {@link #startServer()} or {@link #startServer(String)}.  Similarly, extra
 * teardown goes in an overriding {@link #tearDown()} that calls {@code super.tearDown()}.
 */
public abstract class ProtocolTestBase {

    /** Timeout for operations that involve an OpenJML run (--check, --esc). */
    protected static final long TIMEOUT_SECONDS = 120;
    /** Short timeout for fast server responses (initialize, codeLens, etc.). */
    protected static final long SHORT_TIMEOUT   =   5;

    protected OpenJMLLanguageServer server;
    protected RawLspClient          client;

    @Before
    public void setUp() throws Exception {
        startServer();
    }

    @After
    public void tearDown() {
        if (client != null) client.stop();
    }

    // -----------------------------------------------------------------------
    // Server lifecycle
    // -----------------------------------------------------------------------

    /**
     * Create a server/client pipe connection without completing the initialize handshake.
     * Use this when individual tests need to control the initialize exchange themselves.
     */
    protected void createServerAndClient() throws Exception {
        PipedInputStream  serverIn  = new PipedInputStream(65536);
        PipedOutputStream clientOut = new PipedOutputStream(serverIn);
        PipedInputStream  clientIn  = new PipedInputStream(65536);
        PipedOutputStream serverOut = new PipedOutputStream(clientIn);

        server = new OpenJMLLanguageServer();
        var launcher = LSPLauncher.createServerLauncher(server, serverIn, serverOut);
        server.connect(launcher.getRemoteProxy());
        launcher.startListening();

        client = new RawLspClient(clientOut, clientIn);
    }

    /** Start an in-process LSP server with no workspace root. */
    protected void startServer() throws Exception {
        startServer(null);
    }

    /**
     * Start an in-process LSP server and complete the LSP initialization handshake.
     *
     * @param rootUri workspace root URI, or {@code null} for no workspace
     */
    protected void startServer(String rootUri) throws Exception {
        PipedInputStream  serverIn  = new PipedInputStream(65536);
        PipedOutputStream clientOut = new PipedOutputStream(serverIn);
        PipedInputStream  clientIn  = new PipedInputStream(65536);
        PipedOutputStream serverOut = new PipedOutputStream(clientIn);

        server = new OpenJMLLanguageServer();
        var launcher = LSPLauncher.createServerLauncher(server, serverIn, serverOut);
        server.connect(launcher.getRemoteProxy());
        launcher.startListening();

        client = new RawLspClient(clientOut, clientIn);
        String rootParam = rootUri == null ? "null" : "\"" + rootUri + "\"";
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":" + rootParam + ",\"capabilities\":{}}");
        assertNotNull("Server must respond to initialize",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
        client.sendNotification("initialized", "{}");
    }

    // -----------------------------------------------------------------------
    // JSON helpers
    // -----------------------------------------------------------------------

    /**
     * Escape a Java string for embedding as a JSON string value.
     * Handles backslashes, double quotes, and newlines.
     */
    protected static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    // -----------------------------------------------------------------------
    // Document lifecycle notifications
    // -----------------------------------------------------------------------

    protected void didOpen(String uri, String source) throws Exception {
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}");
    }

    protected void didChange(String uri, int version, String source) throws Exception {
        client.sendNotification("textDocument/didChange",
                "{\"textDocument\":{\"uri\":\"" + uri + "\",\"version\":" + version + "},"
                + "\"contentChanges\":[{\"text\":\"" + jsonEscape(source) + "\"}]}");
    }

    protected void didSave(String uri) throws Exception {
        client.sendNotification("textDocument/didSave",
                "{\"textDocument\":{\"uri\":\"" + uri + "\"}}");
    }

    protected void didClose(String uri) throws Exception {
        client.sendNotification("textDocument/didClose",
                "{\"textDocument\":{\"uri\":\"" + uri + "\"}}");
    }

    // -----------------------------------------------------------------------
    // Wait for publishDiagnostics notifications
    // -----------------------------------------------------------------------

    /**
     * Wait for the next {@code textDocument/publishDiagnostics} notification
     * whose URI <em>contains</em> {@code uriFragment}.
     * Useful when only part of the URI is known (e.g. a filename fragment).
     */
    protected JsonObject nextDiagsFor(String uriFragment, long timeout, TimeUnit unit)
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

    /**
     * Wait for the next {@code textDocument/publishDiagnostics} notification
     * whose URI exactly equals {@code uri}.
     */
    protected JsonObject nextDiagsForUri(String uri, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            if (uri.equals(msg.getAsJsonObject("params").get("uri").getAsString()))
                return msg;
        }
    }

    /**
     * Poll {@code textDocument/publishDiagnostics} until a notification arrives
     * for a URI containing {@code uriFragment} with at least one diagnostic.
     * Skips empty notifications (e.g. from CHECKING-state marker clears).
     */
    protected JsonObject nextNonEmptyDiagsFor(String uriFragment, long timeout, TimeUnit unit)
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

    /**
     * Poll until a notification arrives for the exact URI with at least one diagnostic.
     */
    protected JsonObject nextNonEmptyDiagsForUri(String uri, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            JsonObject params = msg.getAsJsonObject("params");
            if (!uri.equals(params.get("uri").getAsString())) continue;
            if (!params.getAsJsonArray("diagnostics").isEmpty()) return msg;
        }
    }

    /**
     * Poll until a notification arrives for the exact URI that contains at least
     * one error-severity {@link DiagnosticConverter#SOURCE_ESC} diagnostic.
     */
    protected JsonObject nextEscErrorDiagsForUri(String uri, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            JsonObject params = msg.getAsJsonObject("params");
            if (!uri.equals(params.get("uri").getAsString())) continue;
            if (hasEscError(params.getAsJsonArray("diagnostics"))) return msg;
        }
    }

    /**
     * Collect up to {@code wantCount} non-empty {@code textDocument/publishDiagnostics}
     * notifications for the exact URI, stopping early if the timeout expires.
     */
    protected List<JsonObject> collectNonEmptyDiagsForUri(String uri, int wantCount,
            long timeout, TimeUnit unit) throws InterruptedException {
        List<JsonObject> result = new ArrayList<>();
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (result.size() < wantCount) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            if (!uri.equals(params.get("uri").getAsString())) continue;
            if (!params.getAsJsonArray("diagnostics").isEmpty()) result.add(msg);
        }
        return result;
    }

    /**
     * Open a document and wait for the initial {@code --check} diagnostics notification.
     * Returns the notification (may have an empty diagnostics array for clean files).
     */
    protected JsonObject openAndWaitForCheck(String uri, String source) throws Exception {
        didOpen(uri, source);
        return nextDiagsFor(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
    }

    // -----------------------------------------------------------------------
    // Commands
    // -----------------------------------------------------------------------

    /**
     * Send {@code workspace/executeCommand} and drain (discard) the response.
     */
    protected void executeCommand(String command, String argsJson) throws Exception {
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + command + "\",\"arguments\":" + argsJson + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    /**
     * Send {@code workspace/executeCommand} with the standard OpenJML 5-element
     * argument list ({@code ["","","","",uri]}) and drain the response.
     */
    protected void executeCommandForUri(String command, String uri) throws Exception {
        executeCommand(command, "[\"\",\"\",\"\",\"\",\"" + uri + "\"]");
    }

    /**
     * Send {@code workspace/executeCommand} with the standard OpenJML 5-element
     * argument list followed by additional path arguments, and drain the response.
     * {@code extraPaths} are appended after the URI at index 4.
     */
    protected void executeCommandForPaths(String command, String... osPaths) throws Exception {
        StringBuilder args = new StringBuilder("[\"\",\"\",\"\",\"\"");
        for (String p : osPaths) args.append(",\"").append(jsonEscape(p)).append("\"");
        args.append("]");
        executeCommand(command, args.toString());
    }

    /**
     * Send {@code workspace/executeCommand} and return the response (useful when
     * the caller needs to inspect it).
     */
    protected JsonObject sendCommand(String command, String argsJson) throws Exception {
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + command + "\",\"arguments\":" + argsJson + "}");
        return client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    // -----------------------------------------------------------------------
    // Code lenses
    // -----------------------------------------------------------------------

    /**
     * Send {@code textDocument/codeLens} and return the lens array, or {@code null}
     * if the server returned null or the request timed out.
     */
    protected JsonArray requestCodeLens(String uri) throws Exception {
        client.sendRequest("textDocument/codeLens",
                "{\"textDocument\":{\"uri\":\"" + uri + "\"}}");
        JsonObject response = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        if (response == null || !response.has("result") || response.get("result").isJsonNull())
            return null;
        return response.getAsJsonArray("result");
    }

    /**
     * Poll code lenses until the first lens title contains {@code expectedSubstring},
     * draining publishDiagnostics notifications between polls.
     *
     * @return the matching title, or the last title seen when the timeout expires
     */
    protected String pollLensTitleUntil(String uri, String expectedSubstring,
                                         long timeoutSeconds) throws Exception {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(timeoutSeconds);
        String last = null;
        while (System.nanoTime() < deadline) {
            JsonArray lenses = requestCodeLens(uri);
            if (lenses != null) {
                for (int i = 0; i < lenses.size(); i++) {
                    JsonObject lens = lenses.get(i).getAsJsonObject();
                    if (!lens.has("command")) continue;
                    String title = lens.getAsJsonObject("command").get("title").getAsString();
                    if (i == 0 || last == null) last = title;
                    if (title.contains(expectedSubstring)) return title;
                }
            }
            client.nextNotification("textDocument/publishDiagnostics", 200, TimeUnit.MILLISECONDS);
        }
        return last;
    }

    /**
     * Return the title of the first code lens that has a {@code command}, or
     * {@code null} if the lens array is empty or null.
     */
    protected static String firstLensTitle(JsonArray lenses) {
        if (lenses == null) return null;
        for (int i = 0; i < lenses.size(); i++) {
            JsonObject lens = lenses.get(i).getAsJsonObject();
            if (lens.has("command"))
                return lens.getAsJsonObject("command").get("title").getAsString();
        }
        return null;
    }

    /**
     * Extract the method-ref argument (index 1) from the first code lens whose
     * argument at index 1 contains {@code nameFragment}, or from any lens when
     * {@code nameFragment} is {@code null}.
     */
    /**
     * Poll code lenses until a method ref containing {@code nameFragment} is available
     * (i.e. the method is not in CHECKING state), then return it.
     * Returns {@code null} if the timeout expires before the ref appears.
     */
    protected String pollExtractMethodRef(String uri, String nameFragment,
                                          long timeoutSeconds) throws Exception {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(timeoutSeconds);
        while (System.nanoTime() < deadline) {
            JsonArray lenses = requestCodeLens(uri);
            String ref = extractMethodRef(lenses, nameFragment);
            if (ref != null) return ref;
            client.nextNotification("textDocument/publishDiagnostics", 200, TimeUnit.MILLISECONDS);
        }
        return null;
    }

    protected static String extractMethodRef(JsonArray lenses, String nameFragment) {
        if (lenses == null) return null;
        for (int i = 0; i < lenses.size(); i++) {
            JsonObject lens = lenses.get(i).getAsJsonObject();
            if (!lens.has("command")) continue;
            JsonArray args = lens.getAsJsonObject("command").getAsJsonArray("arguments");
            if (args == null || args.size() < 3) continue;
            String ref = args.get(2).getAsString();
            if (nameFragment == null || ref.contains(nameFragment)) return ref;
        }
        return null;
    }

    // -----------------------------------------------------------------------
    // Diagnostic inspection helpers
    // -----------------------------------------------------------------------

    /** True if {@code diags} contains any diagnostic whose {@code source} equals {@code source}. */
    protected static boolean hasDiagWithSource(JsonArray diags, String source) {
        for (int i = 0; i < diags.size(); i++) {
            JsonObject d = diags.get(i).getAsJsonObject();
            if (d.has("source") && source.equals(d.get("source").getAsString())) return true;
        }
        return false;
    }

    /** True if {@code diags} contains any Error-severity diagnostic with the given source. */
    protected static boolean hasErrorDiagWithSource(JsonArray diags, String source) {
        for (int i = 0; i < diags.size(); i++) {
            JsonObject d = diags.get(i).getAsJsonObject();
            if (d.has("source") && source.equals(d.get("source").getAsString())
                    && d.has("severity") && d.get("severity").getAsInt() == 1) return true;
        }
        return false;
    }

    /** True if {@code diags} contains any diagnostic from the ESC pass. */
    protected static boolean hasEscDiag(JsonArray diags) {
        return hasDiagWithSource(diags, DiagnosticConverter.SOURCE_ESC);
    }

    /** True if {@code diags} contains any Error-severity diagnostic from the ESC pass. */
    protected static boolean hasEscError(JsonArray diags) {
        return hasErrorDiagWithSource(diags, DiagnosticConverter.SOURCE_ESC);
    }
}
