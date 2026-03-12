package org.openjml.lsp.test;

import org.eclipse.lsp4j.SignatureHelp;
import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.SignatureHelpProvider;

import java.nio.file.Path;

import static org.junit.Assert.*;

/**
 * Tests for {@link SignatureHelpProvider}: textDocument/signatureHelp.
 *
 * <p>Two tiers:
 * <ul>
 *   <li>Text-only tests (call-site detection, no AST needed) — cover
 *       {@link SignatureHelpProvider#findCallSite},
 *       {@link SignatureHelpProvider#countTopLevelCommas},
 *       {@link SignatureHelpProvider#methodNameBefore}, and
 *       {@link SignatureHelpProvider#shortType}.</li>
 *   <li>AST-backed tests — check a small file via {@link CheckRunner}, then
 *       assert that the full {@link SignatureHelp} response has the right
 *       labels and active-parameter index.</li>
 * </ul>
 */
public class SignatureHelpTest {

    // -----------------------------------------------------------------------
    // findCallSite — text-only
    // -----------------------------------------------------------------------

    @Test
    public void testSimpleCall_firstParam() {
        String src = "foo(a";
        var site = SignatureHelpProvider.findCallSite(src, src.length());
        assertNotNull(site);
        assertEquals("foo", site.methodName());
        assertEquals(0, site.activeParam());
    }

    @Test
    public void testSimpleCall_secondParam() {
        String src = "foo(a, b";
        var site = SignatureHelpProvider.findCallSite(src, src.length());
        assertNotNull(site);
        assertEquals("foo", site.methodName());
        assertEquals(1, site.activeParam());
    }

    @Test
    public void testSimpleCall_thirdParam() {
        String src = "foo(a, b, c";
        var site = SignatureHelpProvider.findCallSite(src, src.length());
        assertNotNull(site);
        assertEquals("foo", site.methodName());
        assertEquals(2, site.activeParam());
    }

    @Test
    public void testNestedCallIgnored() {
        // bar( foo(x, y), _cursor_ — outer bar, second param
        String src = "bar(foo(x, y), z";
        var site = SignatureHelpProvider.findCallSite(src, src.length());
        assertNotNull(site);
        assertEquals("bar", site.methodName());
        assertEquals(1, site.activeParam());
    }

    @Test
    public void testConstructor() {
        String src = "new Foo(a, b";
        var site = SignatureHelpProvider.findCallSite(src, src.length());
        assertNotNull(site);
        assertEquals("Foo", site.methodName());
        assertEquals(1, site.activeParam());
    }

    @Test
    public void testNoCall_empty() {
        assertNull(SignatureHelpProvider.findCallSite("abc", 3));
    }

    @Test
    public void testNoCall_closedParen() {
        // cursor after a closed call — not in any call
        String src = "foo(x)";
        assertNull(SignatureHelpProvider.findCallSite(src, src.length()));
    }

    @Test
    public void testJmlContext() {
        // //@ requires helper(x,  ← cursor after comma
        String src = "    //@ requires helper(x, ";
        var site = SignatureHelpProvider.findCallSite(src, src.length());
        assertNotNull(site);
        assertEquals("helper", site.methodName());
        assertEquals(1, site.activeParam());
    }

    @Test
    public void testMethodNameBefore_simple() {
        String src = "foo(";
        assertEquals("foo", SignatureHelpProvider.methodNameBefore(src, 3));
    }

    @Test
    public void testMethodNameBefore_withSpaces() {
        String src = "foo (";
        assertEquals("foo", SignatureHelpProvider.methodNameBefore(src, 4));
    }

    @Test
    public void testMethodNameBefore_afterDot() {
        // obj.method( — we want just "method"
        String src = "obj.method(";
        assertEquals("method", SignatureHelpProvider.methodNameBefore(src, 10));
    }

    @Test
    public void testCountTopLevelCommas_zero() {
        assertEquals(0, SignatureHelpProvider.countTopLevelCommas("a", 0, 1));
    }

    @Test
    public void testCountTopLevelCommas_two() {
        assertEquals(2, SignatureHelpProvider.countTopLevelCommas("a,b,c", 0, 5));
    }

    @Test
    public void testCountTopLevelCommas_nestedIgnored() {
        // "a, foo(x,y), b" — only 2 top-level commas
        assertEquals(2, SignatureHelpProvider.countTopLevelCommas("a, foo(x,y), b", 0, 14));
    }

    // -----------------------------------------------------------------------
    // shortType
    // -----------------------------------------------------------------------

    @Test
    public void testShortType_primitive() {
        assertEquals("int", SignatureHelpProvider.shortType("int"));
        assertEquals("void", SignatureHelpProvider.shortType("void"));
    }

    @Test
    public void testShortType_qualified() {
        assertEquals("String", SignatureHelpProvider.shortType("java.lang.String"));
    }

    @Test
    public void testShortType_generic() {
        assertEquals("List<String>",
                SignatureHelpProvider.shortType("java.util.List<java.lang.String>"));
    }

    @Test
    public void testShortType_alreadySimple() {
        assertEquals("MyClass", SignatureHelpProvider.shortType("MyClass"));
    }

    // -----------------------------------------------------------------------
    // AST-backed: full SignatureHelp from a compiled file
    // -----------------------------------------------------------------------

    // Plain Java — no JML specs that could trigger attribution errors.
    private static final String HELPER_SRC =
            "public class SigHelper {\n" +
            "    public int square(int x) { return x * x; }\n" +
            "    public int add(int a, int b) { return a + b; }\n" +
            "    public String join(String s, int n) { return s; }\n" +
            "}\n";

    private static ASTCache.Entry cachedEntry;

    /** Compile SigHelper.java once and cache the AST entry for the AST-backed tests. */
    private static ASTCache.Entry getOrCompileEntry() throws Exception {
        if (cachedEntry != null) return cachedEntry;
        String root = System.getProperty("lsp.testdata");
        if (root == null) return null;
        Path dir = Path.of(root, "testSignatureHelp");
        dir.toFile().mkdirs();
        Path file = dir.resolve("SigHelper.java");
        java.nio.file.Files.writeString(file, HELPER_SRC);
        String uri = file.toUri().toString();
        OpenJMLSettings settings = new OpenJMLSettings();
        CheckRunner.checkFile(file.toString(), uri, settings);
        cachedEntry = CheckRunner.getASTCache().get(uri);
        return cachedEntry;
    }

    @Test
    public void testAstBacked_squareSignature() throws Exception {
        String root = System.getProperty("lsp.testdata");
        assertNotNull("lsp.testdata must be set", root);
        ASTCache.Entry entry = getOrCompileEntry();
        assertNotNull("AST cache entry expected after checkFile", entry);

        // Synthetic snippet: cursor is inside "square(" at position after the '('
        String snippet = "square(";
        SignatureHelp help = SignatureHelpProvider.compute(
                snippet, 0, snippet.length(), entry);

        assertNotNull("Expected SignatureHelp for square", help);
        assertFalse("Expected at least one signature", help.getSignatures().isEmpty());
        String label = help.getSignatures().get(help.getActiveSignature()).getLabel();
        assertTrue("Label should contain 'square'", label.contains("square"));
        assertTrue("Label should contain 'int x'", label.contains("int x"));
        assertEquals("First param active", 0, (int) help.getActiveParameter());
    }

    @Test
    public void testAstBacked_addSecondParam() throws Exception {
        String root = System.getProperty("lsp.testdata");
        assertNotNull("lsp.testdata must be set", root);
        ASTCache.Entry entry = getOrCompileEntry();
        assertNotNull("AST cache entry expected after checkFile", entry);

        // Synthetic snippet: cursor is after the comma in "add(1, "
        String snippet = "add(1, ";
        SignatureHelp help = SignatureHelpProvider.compute(
                snippet, 0, snippet.length(), entry);

        assertNotNull("Expected SignatureHelp for add", help);
        String label = help.getSignatures().get(help.getActiveSignature()).getLabel();
        assertTrue("Label should contain 'add'", label.contains("add"));
        assertEquals("Second param active", 1, (int) help.getActiveParameter());
    }
}
