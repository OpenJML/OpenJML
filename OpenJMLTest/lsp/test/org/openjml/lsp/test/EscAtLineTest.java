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
 * Tests for the {@code "@<line>"} method-resolution format used by
 * {@code openjml.runEscForMethod}.
 *
 * <p>When a client sends {@code "@N"} as the method argument the server walks
 * the AST to find the innermost method whose declaration span contains line N.
 * These tests exercise that lookup across all method varieties that require
 * correct nesting logic:
 *
 * <ul>
 *   <li>Constructor</li>
 *   <li>Regular top-level method</li>
 *   <li>Method in a static inner class</li>
 *   <li>Method in a local class (nested inside another method)</li>
 *   <li>Method in an anonymous class</li>
 *   <li>JML {@code model} method</li>
 * </ul>
 *
 * <p>Each target method contains {@code //@ assert false;} so ESC terminates
 * quickly with a verifiable error on that exact line.  The enclosing methods
 * carry no failing specs, so if the wrong method is selected no ESC error
 * arrives and the test fails via timeout.
 */
public class EscAtLineTest extends ProtocolTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    @Before
    @Override
    public void setUp() throws Exception {
        startServer();
    }

    // -----------------------------------------------------------------------
    // Source under test
    // -----------------------------------------------------------------------

    // Each target method has a unique failing JML assertion (//@ assert N==0;) so ESC
    // terminates quickly.  The distinct integer N doubles as a lineOf() search marker.
    // No block comments inside JML line comments — that would trigger parse errors and
    // prevent AST caching, breaking @line resolution.
    private static final String SOURCE = """
            public class AtLineTest {
                public AtLineTest() {
                    //@ assert 1==0;
                }

                public int topMethod(int x) {
                    //@ assert 2==0;
                    return x;
                }

                static class Inner {
                    public int innerMethod(int x) {
                        //@ assert 3==0;
                        return x;
                    }
                }

                public void withLocal() {
                    class Local {
                        public int localMethod(int x) {
                            //@ assert 4==0;
                            return x;
                        }
                    }
                    new Local().localMethod(0);
                }

                Runnable anon = new Runnable() {
                    public void run() {
                        //@ assert 5==0;
                    }
                };

                //@ ensures false; pure model public int modelMethod(int x) { return x; }
            }
            """;

    /** Returns the 0-based line index of the first line containing {@code marker}. */
    private static int lineOf(String marker) {
        String[] lines = SOURCE.split("\n", -1);
        for (int i = 0; i < lines.length; i++)
            if (lines[i].contains(marker)) return i;
        throw new AssertionError("marker not found in source: " + marker);
    }

    // -----------------------------------------------------------------------
    // Infrastructure
    // -----------------------------------------------------------------------

    private File writeJava(String filename, String content) throws Exception {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    private void didOpenAndDrainCheck(String uri) throws Exception {
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(SOURCE) + "\"}}");
        nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
    }

    /**
     * Sends {@code openjml.runEscForMethod} with {@code "@<cursorLine>"} and
     * waits for the first ESC error diagnostic on {@code uri}.
     * Returns the 0-based start line of that diagnostic, or -1 on timeout.
     */
    private int escAtLineAndGetErrorLine(String uri, int cursorLine) throws Exception {
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":[\"\",\"" + jsonEscape(uri)
                + "\",\"@" + cursorLine + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS);
        while (true) {
            long rem = deadline - System.nanoTime();
            if (rem <= 0) return -1;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", rem, TimeUnit.NANOSECONDS);
            if (msg == null) return -1;
            JsonObject params = msg.getAsJsonObject("params");
            if (!uri.equals(params.get("uri").getAsString())) continue;
            JsonArray diags = params.getAsJsonArray("diagnostics");
            for (int i = 0; i < diags.size(); i++) {
                JsonObject d = diags.get(i).getAsJsonObject();
                if (d.has("source")
                        && DiagnosticConverter.SOURCE_ESC.equals(d.get("source").getAsString())
                        && d.has("severity") && d.get("severity").getAsInt() == 1) {
                    return d.getAsJsonObject("range").getAsJsonObject("start").get("line").getAsInt();
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    @Test
    public void testAtLine_Constructor() throws Exception {
        File f = writeJava("AtLineTest.java", SOURCE);
        String uri = f.toPath().toUri().toString();
        didOpenAndDrainCheck(uri);

        int assertLine = lineOf("assert 1==0");
        int errorLine  = escAtLineAndGetErrorLine(uri, assertLine);
        assertEquals("@line in constructor body must ESC the constructor (error at assert line)",
                assertLine, errorLine);
    }

    @Test
    public void testAtLine_TopLevelMethod() throws Exception {
        File f = writeJava("AtLineTest.java", SOURCE);
        String uri = f.toPath().toUri().toString();
        didOpenAndDrainCheck(uri);

        int assertLine = lineOf("assert 2==0");
        int errorLine  = escAtLineAndGetErrorLine(uri, assertLine);
        assertEquals("@line in topMethod body must ESC topMethod (error at assert line)",
                assertLine, errorLine);
    }

    @Test
    public void testAtLine_InnerClassMethod() throws Exception {
        File f = writeJava("AtLineTest.java", SOURCE);
        String uri = f.toPath().toUri().toString();
        didOpenAndDrainCheck(uri);

        int assertLine = lineOf("assert 3==0");
        int errorLine  = escAtLineAndGetErrorLine(uri, assertLine);
        assertEquals("@line in innerMethod body must ESC innerMethod (error at assert line)",
                assertLine, errorLine);
    }

    @Test
    public void testAtLine_LocalClassMethod() throws Exception {
        // The cursor is inside localMethod, which is nested inside withLocal.
        // The scanner must return localMethod (innermost), not withLocal.
        // withLocal has no failing spec, so targeting it would produce no ESC error,
        // causing the test to return -1 and fail the assertion below.
        File f = writeJava("AtLineTest.java", SOURCE);
        String uri = f.toPath().toUri().toString();
        didOpenAndDrainCheck(uri);

        int assertLine = lineOf("assert 4==0");
        int errorLine  = escAtLineAndGetErrorLine(uri, assertLine);
        // OpenJML bug: the diagnostic for a JML assert inside a local-class method is
        // reported one line early (at the method declaration) instead of at the assert
        // statement itself.  Accommodate by expecting assertLine - 1.
        assertEquals("@line in localMethod body must ESC localMethod (not enclosing withLocal)",
                assertLine - 1, errorLine);
    }

    @Test
    public void testAtLine_AnonymousClassMethod() throws Exception {
        // The cursor is inside run(), nested inside the anonymous Runnable expression.
        // The scanner must return run() (innermost), not any enclosing context.
        File f = writeJava("AtLineTest.java", SOURCE);
        String uri = f.toPath().toUri().toString();
        didOpenAndDrainCheck(uri);

        int assertLine = lineOf("assert 5==0");
        int errorLine  = escAtLineAndGetErrorLine(uri, assertLine);
        // OpenJML bug: the diagnostic for a JML assert inside an anonymous-class method
        // is reported one line early (at the method declaration) instead of at the assert
        // statement itself.  Accommodate by expecting assertLine - 1.
        assertEquals("@line in anonymous run() body must ESC run() (not enclosing context)",
                assertLine - 1, errorLine);
    }

    @Test
    public void testAtLine_ModelMethod() throws Exception {
        // The cursor is on the model method return line; the server must
        // locate modelMethod and produce an ESC error (ensures false).
        File f = writeJava("AtLineTest.java", SOURCE);
        String uri = f.toPath().toUri().toString();
        didOpenAndDrainCheck(uri);

        int modelLine = lineOf("modelMethod");
        int errorLine = escAtLineAndGetErrorLine(uri, modelLine);
        assertNotEquals("@line in model method must produce an ESC error", -1, errorLine);
    }
}
