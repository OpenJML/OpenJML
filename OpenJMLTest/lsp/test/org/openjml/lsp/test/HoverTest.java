package org.openjml.lsp.test;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for {@code textDocument/hover}.
 *
 * <p>The server's hover provider:
 * <ul>
 *   <li>Returns the JML spec lines above the enclosing method when the cursor
 *       is inside a method that has JML annotations.</li>
 *   <li>Returns {@code null} when the cursor is inside a method with no JML.</li>
 *   <li>Returns the inferred type for a {@code var} declaration when the cursor
 *       is on the variable (via {@link org.openjml.lsp.InlayHintProvider}).</li>
 * </ul>
 *
 * <p>These tests drive the full JSON-RPC path via {@link RawLspClient} and assert
 * on the hover response content.
 */
public class HoverTest extends ProtocolTestBase {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Send a {@code textDocument/hover} request at the given position.
     *
     * @param uri    document URI
     * @param line   0-based line number
     * @param col    0-based column number
     * @return       the raw JSON-RPC response object
     */
    private JsonObject sendHoverRequest(String uri, int line, int col)
            throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\"},"
                + "\"position\":{\"line\":" + line + ",\"character\":" + col + "}}";
        client.sendRequest("textDocument/hover", params);
        return client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    // -----------------------------------------------------------------------
    // Hover returns JML spec for annotated method
    // -----------------------------------------------------------------------

    /**
     * Hovering inside a method that has JML annotations above it must return
     * a Markdown hover response containing the JML clause text and the method name.
     *
     * <p>Source layout (0-based lines):
     * <pre>
     *   0: public class HoverJml {
     *   1:     //@ ensures \result >= 0;
     *   2:     public int m() { return 42; }
     *   3: }
     * </pre>
     * Hovering at line 2, col 20 (inside the method body) must return
     * a Markdown hover with content referencing {@code m} and the spec.
     */
    @Test
    public void testHoverOnMethodWithJmlSpec() throws Exception {
        String uri    = "file:///HoverJml.java";
        String source = "public class HoverJml {\n"
                + "    //@ ensures \\result >= 0;\n"
                + "    public int m() { return 42; }\n"
                + "}\n";
        didOpen(uri, source);
        // Wait for the open-triggered --check so lastContent is populated.
        nextDiagsFor("HoverJml", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Hover at line 2 (the method body), col 20 (inside the braces).
        JsonObject response = sendHoverRequest(uri, 2, 20);
        assertNotNull("Expected a hover response", response);
        assertFalse("Hover result must not be null", response.get("result").isJsonNull());

        JsonObject result = response.getAsJsonObject("result");
        assertTrue("Hover result must have 'contents'", result.has("contents"));
        JsonObject contents = result.getAsJsonObject("contents");
        String value = contents.get("value").getAsString();
        assertTrue("Hover must reference the method name 'm'", value.contains("m"));
        assertTrue("Hover must contain the JML clause", value.contains("ensures"));
    }

    // -----------------------------------------------------------------------
    // Hover returns null for method without JML spec
    // -----------------------------------------------------------------------

    /**
     * Hovering inside a method that has no JML annotations must return a null
     * (or absent) result — the server should not invent content.
     *
     * <p>Source layout (0-based lines):
     * <pre>
     *   0: public class HoverNoJml {
     *   1:     public int add(int a, int b) { return a + b; }
     *   2: }
     * </pre>
     * Hovering at line 1, col 30 (inside the method body) must return null.
     */
    @Test
    public void testHoverOnMethodWithoutJmlSpec() throws Exception {
        String uri    = "file:///HoverNoJml.java";
        String source = "public class HoverNoJml {\n"
                + "    public int add(int a, int b) { return a + b; }\n"
                + "}\n";
        didOpen(uri, source);
        nextDiagsFor("HoverNoJml", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Hover at line 1, col 30 (inside the method body — no JML above it).
        JsonObject response = sendHoverRequest(uri, 1, 30);
        assertNotNull("Expected a JSON-RPC response (even if result is null)", response);
        // The server returns null when there is no JML spec to show.
        assertTrue("Hover result must be null for a method without JML spec",
                response.get("result").isJsonNull());
    }

    // -----------------------------------------------------------------------
    // Hover on method with multi-clause JML spec
    // -----------------------------------------------------------------------

    /**
     * Hovering inside a method that has multiple JML clauses must return all
     * clauses in the response, not just the first.
     *
     * <p>Source layout (0-based lines):
     * <pre>
     *   0: public class HoverMultiClause {
     *   1:     //@ requires x >= 0;
     *   2:     //@ ensures \result >= 0;
     *   3:     public int m(int x) { return x + 1; }
     *   4: }
     * </pre>
     */
    @Test
    public void testHoverOnMethodWithMultipleJmlClauses() throws Exception {
        String uri    = "file:///HoverMultiClause.java";
        String source = "public class HoverMultiClause {\n"
                + "    //@ requires x >= 0;\n"
                + "    //@ ensures \\result >= 0;\n"
                + "    public int m(int x) { return x + 1; }\n"
                + "}\n";
        didOpen(uri, source);
        nextDiagsFor("HoverMultiClause", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Hover at line 3 (the method body).
        JsonObject response = sendHoverRequest(uri, 3, 20);
        assertNotNull("Expected a hover response", response);
        assertFalse("Hover result must not be null", response.get("result").isJsonNull());

        JsonObject result = response.getAsJsonObject("result");
        JsonObject contents = result.getAsJsonObject("contents");
        String value = contents.get("value").getAsString();
        assertTrue("Hover must contain 'requires'", value.contains("requires"));
        assertTrue("Hover must contain 'ensures'",  value.contains("ensures"));
    }
}
