package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for {@code textDocument/documentHighlight}.
 *
 * <p>Each test starts a fresh in-process LSP server so server state does not leak
 * between tests.  A temporary directory is created per test and torn down in
 * {@code @After}.
 *
 * <h3>Matching semantics</h3>
 * The server implements <em>identifier-name matching</em>: every AST node whose
 * {@code name} field equals the token under the cursor is highlighted, regardless of
 * which compiler symbol it resolves to.  This means:
 * <ul>
 *   <li>Declaration sites are included.</li>
 *   <li>Multiple symbols with the same name (e.g. a parameter {@code x} and a field
 *       {@code x} visible via inheritance) will both be highlighted.</li>
 *   <li>Occurrences inside string literals and comments are <em>not</em> reported
 *       because the AST does not produce identifier nodes for those regions.</li>
 * </ul>
 *
 * <h3>Coverage targets</h3>
 * <ul>
 *   <li>{@link #testHighlightLocalVariableInJavaFile} — cursor on a local variable
 *       in a {@code .java} file; expect the declaration site and every use.</li>
 *   <li>{@link #testHighlightParameterInJavaFile} — cursor on a parameter name;
 *       expect the parameter declaration and every use in the method body.</li>
 *   <li>{@link #testHighlightNoResultForNonIdentifier} — cursor on an operator
 *       character; expect an empty result.</li>
 *   <li>{@link #testHighlightInJmlFile} — cursor on an identifier that appears in
 *       a {@code .jml} spec file; expect highlights within the {@code .jml}
 *       source only.</li>
 * </ul>
 */
public class DocumentHighlightTest extends ProtocolTestBase {

    private Path tmpDir;

    // -----------------------------------------------------------------------
    // Per-test lifecycle
    // -----------------------------------------------------------------------

    @Before
    @Override
    public void setUp() throws Exception {
        tmpDir = Files.createTempDirectory("DocumentHighlightTest-");
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

    private static String fileUri(Path p) {
        return p.toUri().toString();
    }

    /**
     * Open a file via {@code textDocument/didOpen} and wait for the initial
     * {@code textDocument/publishDiagnostics} so we know the AST is cached.
     */
    private void openAndWait(String uri, String source) throws Exception {
        didOpen(uri, source);
        // Wait for the initial check to complete (AST is stored before diags are published).
        JsonObject diags = nextDiagsFor(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen for " + uri, diags);
    }

    /**
     * Send {@code textDocument/documentHighlight} and return the result array
     * (may be {@code null} if the server returns a null result).
     */
    private JsonArray sendHighlight(String uri, int line, int col) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\"},"
                + "\"position\":{\"line\":" + line + ",\"character\":" + col + "}}";
        client.sendRequest("textDocument/documentHighlight", params);
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to documentHighlight", resp);
        if (resp.get("result").isJsonNull()) return null;
        return resp.getAsJsonArray("result");
    }

    /**
     * Count highlights in {@code arr} that start on the given 0-indexed {@code line}.
     */
    private static int highlightsOnLine(JsonArray arr, int line) {
        int count = 0;
        for (var el : arr) {
            int startLine = el.getAsJsonObject()
                    .getAsJsonObject("range")
                    .getAsJsonObject("start")
                    .get("line").getAsInt();
            if (startLine == line) count++;
        }
        return count;
    }

    // -----------------------------------------------------------------------
    // Test 1 — local variable in a .java file
    // -----------------------------------------------------------------------

    /**
     * Open a Java file where a local variable {@code sum} appears on two lines:
     * the declaration ({@code int sum = x + y;}) and the return statement
     * ({@code return sum;}).  Put the cursor on the declaration occurrence and
     * verify that exactly two highlights are returned — one on each of those lines.
     *
     * <pre>
     * line 0:  public class HighlightJava {
     * line 1:      public int add(int x, int y) {
     * line 2:          int sum = x + y;          // sum at col 12
     * line 3:          return sum;               // sum at col 15
     * line 4:      }
     * line 5:  }
     * </pre>
     */
    @Test
    public void testHighlightLocalVariableInJavaFile() throws Exception {
        String source =
                "public class HighlightJava {\n"
                + "    public int add(int x, int y) {\n"
                + "        int sum = x + y;\n"   // line 2: sum at col 12
                + "        return sum;\n"          // line 3: sum at col 15
                + "    }\n"
                + "}\n";

        Path file = tmpDir.resolve("HighlightJava.java");
        Files.writeString(file, source, StandardCharsets.UTF_8);
        String uri = fileUri(file);

        openAndWait(uri, source);

        // Cursor on "sum" at line 2, col 12 (declaration site).
        JsonArray highlights = sendHighlight(uri, 2, 12);
        assertNotNull("documentHighlight must return a non-null result", highlights);
        assertEquals("'sum' appears on 2 lines → 2 highlights expected", 2, highlights.size());
        assertEquals("One highlight on line 2 (declaration)", 1, highlightsOnLine(highlights, 2));
        assertEquals("One highlight on line 3 (use in return)", 1, highlightsOnLine(highlights, 3));
    }

    // -----------------------------------------------------------------------
    // Test 2 — parameter name in a .java file
    // -----------------------------------------------------------------------

    /**
     * The parameter {@code x} is declared at line 1 col 23 and used at line 2 col 18.
     * Put the cursor on the parameter declaration; verify two highlights are returned.
     *
     * <pre>
     * line 1:      public int add(int x, int y) {   // x at col 23
     * line 2:          int sum = x + y;              // x at col 18
     * </pre>
     */
    @Test
    public void testHighlightParameterInJavaFile() throws Exception {
        String source =
                "public class HighlightJava {\n"
                + "    public int add(int x, int y) {\n"   // line 1: x at col 23
                + "        int sum = x + y;\n"              // line 2: x at col 18
                + "        return sum;\n"
                + "    }\n"
                + "}\n";

        Path file = tmpDir.resolve("HighlightJava.java");
        Files.writeString(file, source, StandardCharsets.UTF_8);
        String uri = fileUri(file);

        openAndWait(uri, source);

        // Cursor on "x" at line 1, col 23 (parameter declaration).
        JsonArray highlights = sendHighlight(uri, 1, 23);
        assertNotNull("documentHighlight must return a non-null result", highlights);
        // x appears as: parameter declaration (line 1) + use in body (line 2) = 2
        assertEquals("'x' appears on 2 lines → 2 highlights expected", 2, highlights.size());
        assertEquals("One highlight on line 1 (parameter decl)", 1, highlightsOnLine(highlights, 1));
        assertEquals("One highlight on line 2 (use in expression)", 1, highlightsOnLine(highlights, 2));
    }

    // -----------------------------------------------------------------------
    // Test 3 — cursor on a non-identifier character
    // -----------------------------------------------------------------------

    /**
     * Put the cursor on the {@code +} operator at line 2 col 20.  The server must
     * return an empty (or null) result — no highlights for non-identifier positions.
     */
    @Test
    public void testHighlightNoResultForNonIdentifier() throws Exception {
        String source =
                "public class HighlightJava {\n"
                + "    public int add(int x, int y) {\n"
                + "        int sum = x + y;\n"   // '+' at col 20
                + "        return sum;\n"
                + "    }\n"
                + "}\n";

        Path file = tmpDir.resolve("HighlightJava.java");
        Files.writeString(file, source, StandardCharsets.UTF_8);
        String uri = fileUri(file);

        openAndWait(uri, source);

        // Cursor on '+' at line 2, col 20.
        JsonArray highlights = sendHighlight(uri, 2, 20);
        // Either null result or empty array is acceptable.
        assertTrue("No highlights expected for non-identifier position",
                highlights == null || highlights.size() == 0);
    }

    // -----------------------------------------------------------------------
    // Test 4 — identifier in a .jml file
    // -----------------------------------------------------------------------

    /**
     * Create a companion {@code .jml} spec file for {@code HighlightJml.java}.  The
     * spec file contains a {@code requires} clause that references the parameter {@code n}
     * and an {@code ensures} clause that references {@code \result} and {@code n}.
     *
     * <p>Open the {@code .jml} file; the server redirects the check to the companion
     * {@code .java} so the specs CU is cached.  Put the cursor on {@code n} in the
     * {@code requires} clause and verify that at least two highlights are returned —
     * the {@code requires} occurrence and the {@code ensures} occurrence — both within
     * the {@code .jml} source.
     *
     * <pre>
     * HighlightJml.jml:
     * line 0:  public class HighlightJml {
     * line 1:      //@ requires n >= 0;        // n at col 17
     * line 2:      //@ ensures \result == n;   // n at col 23
     * line 3:      public int abs(int n);
     * line 4:  }
     * </pre>
     */
    @Test
    public void testHighlightInJmlFile() throws Exception {
        // Companion .java file — minimal class declaration so the compiler accepts it.
        String javaSrc =
                "public class HighlightJml {\n"
                + "    public int abs(int n) { return n < 0 ? -n : n; }\n"
                + "}\n";
        Path javaFile = tmpDir.resolve("HighlightJml.java");
        Files.writeString(javaFile, javaSrc, StandardCharsets.UTF_8);

        // .jml spec file: n appears in the requires clause (line 1 col 18) and in the
        // ensures clause (line 2 col 23).  It also appears in the abstract method
        // signature (line 3).
        String jmlSrc =
                "public class HighlightJml {\n"
                + "    //@ requires n >= 0;\n"          // line 1: n at col 17
                + "    //@ ensures \\result == n;\n"    // line 2: n at col 23
                + "    public int abs(int n);\n"        // line 3: n at col 23
                + "}\n";
        Path jmlFile = tmpDir.resolve("HighlightJml.jml");
        Files.writeString(jmlFile, jmlSrc, StandardCharsets.UTF_8);

        String jmlUri  = fileUri(jmlFile);
        String javaUri = fileUri(javaFile);

        // Configure specsPath to the temp directory so OpenJML finds HighlightJml.jml
        // when it looks for companion specs alongside HighlightJml.java.
        String specsDirEscaped = jsonEscape(tmpDir.toAbsolutePath().toString());
        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":{\"openjml\":{\"specsPath\":\"" + specsDirEscaped + "\"}}}");
        Thread.sleep(100);

        // Open the .jml file.  The server redirects the check to HighlightJml.java.
        // With specsPath including tmpDir, OpenJML finds HighlightJml.jml on disk and
        // populates specsCompilationUnit; cacheSpecsCu then stores the specs AST under
        // the .jml URI so documentHighlight can find it.
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + jmlUri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(jmlSrc) + "\"}}");

        // The check runs on the .java companion; drain its publishDiagnostics.
        JsonObject diags = nextDiagsFor("HighlightJml.java", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after opening .jml file", diags);

        // Small pause to ensure the AST is fully stored in the cache.
        Thread.sleep(200);

        // Cursor on "n" in the requires clause: line 1, col 17.
        // "    //@ requires n >= 0;" — 4 spaces + "//@ requires " (13 chars) = col 17.
        JsonArray highlights = sendHighlight(jmlUri, 1, 17);
        assertNotNull("documentHighlight must return a non-null result for .jml file", highlights);
        assertTrue("'n' should appear at least twice in the .jml source (requires + ensures)",
                highlights.size() >= 2);
        // Verify all highlights are within the .jml source (no .java line numbers bleed through).
        // The .jml file has 5 lines (0–4); all highlight start lines must be in that range.
        for (var el : highlights) {
            int startLine = el.getAsJsonObject()
                    .getAsJsonObject("range")
                    .getAsJsonObject("start")
                    .get("line").getAsInt();
            assertTrue("All highlights must be within the .jml file (line 0–4), got line "
                    + startLine, startLine >= 0 && startLine <= 4);
        }
    }
}
