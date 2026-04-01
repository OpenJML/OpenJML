package org.openjml.lsp.test;

import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.SignatureHelp;
import org.eclipse.lsp4j.SignatureHelpParams;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.SignatureHelpProvider;

import static org.junit.Assert.*;

/**
 * Tests for {@link SignatureHelpProvider}: textDocument/signatureHelp.
 *
 * <p>Each test populates the AST cache via {@link CheckRunner#check} (using a
 * syntactically valid source) and then calls
 * {@link SignatureHelpProvider#compute} directly, passing the source string
 * separately (as the service does from {@code lastContent}).  The cursor is
 * placed inside a method call argument list; the provider must return a
 * {@link SignatureHelp} that identifies the correct signature and
 * active-parameter index.
 */
public class SignatureHelpTest extends LspTestBase {

    private static final String URI = "file:///SigHelp.java";

    /** Helper: build SignatureHelpParams for a 0-indexed (line, col) position. */
    private static SignatureHelpParams at(String uri, int line, int col) {
        return new SignatureHelpParams(
                new TextDocumentIdentifier(uri),
                new Position(line, col),
                null);
    }

    // -----------------------------------------------------------------------
    // (1) Cursor right after open paren: activeParameter = 0
    // -----------------------------------------------------------------------

    @Test
    public void testSignatureHelpAtOpenParen() {
        // Source is syntactically valid so the AST is fully attributed.
        // Cursor is placed on the '1' in 'add(1, 2)' — right after '(',
        // which is activeParameter=0.
        //
        // Line 2: "    public void caller() { int x = add(1, 2); }"
        //          0         1         2         3
        //          0123456789012345678901234567890123456789
        //                                            ^ col 39 = '1'
        String source =
                "public class SigHelp {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "    public void caller() { int x = add(1, 2); }\n" +
                "}\n";
        checkContent(URI, source);
        int line = 2;
        int col = 39;  // character '1', just inside '('
        SignatureHelp result = SignatureHelpProvider.compute(at(URI, line, col), source,
                CheckRunner.getASTCache());

        assertNotNull("Expected non-null SignatureHelp", result);
        assertFalse("Expected at least one signature", result.getSignatures().isEmpty());
        assertEquals("Expected activeParameter=0", Integer.valueOf(0), result.getActiveParameter());
        String label = result.getSignatures().get(0).getLabel();
        assertTrue("Label must contain 'add'", label.contains("add"));
        assertTrue("Label must contain 'int a'", label.contains("int a"));
        assertTrue("Label must contain 'int b'", label.contains("int b"));
    }

    // -----------------------------------------------------------------------
    // (2) Cursor after comma: activeParameter = 1
    // -----------------------------------------------------------------------

    @Test
    public void testSignatureHelpAfterComma() {
        // Cursor is on '2' in 'add(1, 2)' — after the comma — activeParameter=1.
        //
        // Line 2: "    public void caller() { int x = add(1, 2); }"
        //          0         1         2         3         4
        //          01234567890123456789012345678901234567890123456789
        //                                              ^ col 42 = '2'
        String source =
                "public class SigHelp {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "    public void caller() { int x = add(1, 2); }\n" +
                "}\n";
        checkContent(URI, source);
        int line = 2;
        int col = 42;  // character '2', after ', '
        SignatureHelp result = SignatureHelpProvider.compute(at(URI, line, col), source,
                CheckRunner.getASTCache());

        assertNotNull("Expected non-null SignatureHelp", result);
        assertFalse("Expected at least one signature", result.getSignatures().isEmpty());
        assertEquals("Expected activeParameter=1 after first comma",
                Integer.valueOf(1), result.getActiveParameter());
    }

    // -----------------------------------------------------------------------
    // (3) Cursor outside any call: empty response
    // -----------------------------------------------------------------------

    @Test
    public void testSignatureHelpNotInCall() {
        // Cursor is on 'x' in 'int x = 1' — not inside any call.
        String source =
                "public class SigHelp {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "    public void caller() { int x = 1; }\n" +
                "}\n";
        checkContent(URI, source);
        int line = 2;
        int col = 32;  // 'x'
        SignatureHelp result = SignatureHelpProvider.compute(at(URI, line, col), source,
                CheckRunner.getASTCache());

        assertNotNull("Expected non-null SignatureHelp", result);
        assertTrue("Expected empty signatures when not in a call",
                result.getSignatures() == null || result.getSignatures().isEmpty());
    }

    // -----------------------------------------------------------------------
    // (4) No AST (file not yet checked): graceful empty response
    // -----------------------------------------------------------------------

    @Test
    public void testSignatureHelpNoAst() {
        // Deliberately do NOT call checkContent — no AST in cache.
        String uri = "file:///SigHelpNoAst.java";
        CheckRunner.getASTCache().remove(uri);
        String source =
                "public class SigHelpNoAst {\n" +
                "    public void caller() { foo(1, 2); }\n" +
                "}\n";

        // Line 1, col 32: inside 'foo(1'
        SignatureHelp result = SignatureHelpProvider.compute(at(uri, 1, 32), source,
                CheckRunner.getASTCache());

        assertNotNull("Expected non-null SignatureHelp even without AST", result);
        assertTrue("Expected empty signatures when no AST available",
                result.getSignatures() == null || result.getSignatures().isEmpty());
    }

    // -----------------------------------------------------------------------
    // (5) Nested call: cursor inside inner call returns inner method's signature
    // -----------------------------------------------------------------------

    @Test
    public void testSignatureHelpNestedCall() {
        // Source layout:
        // line 0: public class SigHelp {
        // line 1:     public int add(int a, int b) { return a + b; }
        // line 2:     public int neg(int x) { return -x; }
        // line 3:     public void caller() { int x = add(neg(1), 2); }
        //                                                    ^ col 39 = '1', inside neg(
        // The cursor is inside the inner call neg(1), so the provider should
        // return neg's signature (one parameter), not add's.
        String source =
                "public class SigHelp {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "    public int neg(int x) { return -x; }\n" +
                "    public void caller() { int x = add(neg(1), 2); }\n" +
                "}\n";
        checkContent(URI, source);
        // line 3: "    public void caller() { int x = add(neg(1), 2); }"
        //          0         1         2         3         4
        //          0123456789012345678901234567890123456789012345678901
        //                                              ^ col 43 = '1', inside neg(
        int line = 3;
        int col = 43;
        SignatureHelp result = SignatureHelpProvider.compute(at(URI, line, col), source,
                CheckRunner.getASTCache());

        assertNotNull("Expected non-null SignatureHelp for nested call", result);
        assertFalse("Expected at least one signature", result.getSignatures().isEmpty());
        String label = result.getSignatures().get(0).getLabel();
        assertTrue("Label must be for 'neg', the inner call", label.contains("neg"));
    }

    // -----------------------------------------------------------------------
    // (6) Field-access receiver: this.method(args) — finds the declaration
    // -----------------------------------------------------------------------

    @Test
    public void testSignatureHelpWithThisReceiver() {
        // Source layout:
        // line 0: public class SigHelp {
        // line 1:     public int add(int a, int b) { return a + b; }
        // line 2:     public void caller() { int x = this.add(1, 2); }
        // line 3: }
        // Cursor at '1' (col 44), inside this.add(
        String source =
                "public class SigHelp {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "    public void caller() { int x = this.add(1, 2); }\n" +
                "}\n";
        checkContent(URI, source);
        // line 2: "    public void caller() { int x = this.add(1, 2); }"
        //          0         1         2         3         4
        //          01234567890123456789012345678901234567890123456789012
        //                                                  ^ col 44 = '1'
        int line = 2;
        int col = 44;
        SignatureHelp result = SignatureHelpProvider.compute(at(URI, line, col), source,
                CheckRunner.getASTCache());

        assertNotNull("Expected non-null SignatureHelp for this.add(", result);
        assertFalse("Expected at least one signature for 'add'", result.getSignatures().isEmpty());
        String label = result.getSignatures().get(0).getLabel();
        assertTrue("Label must contain 'add'", label.contains("add"));
        assertEquals("Expected activeParameter=0 for first arg", Integer.valueOf(0), result.getActiveParameter());
    }

    // -----------------------------------------------------------------------
    // (7) Method with JML requires: signature label is present
    // -----------------------------------------------------------------------

    @Test
    public void testSignatureHelpWithJmlMethod() {
        // Cursor on '5' in 'abs(5)' — inside the call.
        //
        // Line 4: "    public void caller() { int x = abs(5); }"
        //          0         1         2         3
        //          0123456789012345678901234567890123456789
        //                                            ^ col 39 = '5'
        String source =
                "public class SigHelp {\n" +
                "    //@ requires n >= 0;\n" +
                "    //@ ensures \\result >= 0;\n" +
                "    public int abs(int n) { return n < 0 ? -n : n; }\n" +
                "    public void caller() { int x = abs(5); }\n" +
                "}\n";
        checkContent(URI, source);
        int line = 4;
        int col = 39;  // '5', just inside 'abs('
        SignatureHelp result = SignatureHelpProvider.compute(at(URI, line, col), source,
                CheckRunner.getASTCache());

        assertNotNull("Expected non-null SignatureHelp", result);
        assertFalse("Expected at least one signature for 'abs'", result.getSignatures().isEmpty());
        assertEquals("Expected activeParameter=0", Integer.valueOf(0), result.getActiveParameter());
        String label = result.getSignatures().get(0).getLabel();
        assertTrue("Label must contain 'abs'", label.contains("abs"));
        assertTrue("Label must contain parameter 'int n'", label.contains("int n"));
    }
}
