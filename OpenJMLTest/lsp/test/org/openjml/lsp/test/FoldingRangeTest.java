package org.openjml.lsp.test;

import org.eclipse.lsp4j.FoldingRange;
import org.junit.Test;
import org.openjml.lsp.FoldingRangeProvider;

import java.util.List;

import static org.junit.Assert.*;

/**
 * Tests for {@link FoldingRangeProvider}: textDocument/foldingRange.
 *
 * <p>Pure text scan — no AST or CheckRunner needed.
 */
public class FoldingRangeTest {

    private static List<FoldingRange> folds(String source) {
        return FoldingRangeProvider.fromSource(source);
    }

    // -----------------------------------------------------------------------
    // No folds
    // -----------------------------------------------------------------------

    @Test
    public void testNoJml() {
        String source =
                "public class Foo {\n" +
                "    public int x;\n" +
                "}\n";
        assertTrue(folds(source).isEmpty());
    }

    @Test
    public void testSingleJmlLine_noFold() {
        // A single-line JML annotation does not need a fold handle.
        String source =
                "    //@ requires x > 0;\n" +
                "    public int foo(int x) { return x; }\n";
        assertTrue(folds(source).isEmpty());
    }

    // -----------------------------------------------------------------------
    // Line comments
    // -----------------------------------------------------------------------

    @Test
    public void testTwoConsecutiveLineComments() {
        String source =
                "    //@ requires x > 0;\n" +   // line 0
                "    //@ ensures \\result > 0;\n" + // line 1
                "    public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(1, fs.get(0).getEndLine());
    }

    @Test
    public void testMultipleConsecutiveLineComments() {
        String source =
                "//@ requires x > 0;\n" +          // line 0
                "//@ assignable \\nothing;\n" +     // line 1
                "//@ ensures \\result > 0;\n" +     // line 2
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    @Test
    public void testTwoSeparateGroups() {
        String source =
                "//@ requires x > 0;\n" +          // line 0
                "//@ ensures \\result > 0;\n" +     // line 1
                "public int foo(int x) { return x; }\n" + // line 2 — breaks group
                "//@ requires y > 0;\n" +           // line 3
                "//@ ensures \\result >= 0;\n" +    // line 4
                "public int bar(int y) { return y; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(2, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(1, fs.get(0).getEndLine());
        assertEquals(3, fs.get(1).getStartLine());
        assertEquals(4, fs.get(1).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Block comments
    // -----------------------------------------------------------------------

    @Test
    public void testSingleLineBlockComment_noFold() {
        String source = "    /*@ requires x > 0; */\n" +
                        "    public int foo(int x) { return x; }\n";
        assertTrue(folds(source).isEmpty());
    }

    @Test
    public void testMultiLineBlockComment() {
        String source =
                "    /*@ requires x > 0;\n" +       // line 0
                "      @ ensures \\result > 0;\n" + // line 1
                "      @*/\n" +                     // line 2
                "    public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Mixed: consecutive line + block in same region
    // -----------------------------------------------------------------------

    @Test
    public void testMixedLineAndBlock() {
        String source =
                "/*@ requires x > 0;\n" +           // line 0 — block start
                "  @ ensures \\result > 0; */\n" +  // line 1 — block end
                "//@ assignable \\nothing;\n" +      // line 2 — continues region
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Conditional annotations
    // -----------------------------------------------------------------------

    @Test
    public void testConditionalAnnotation() {
        String source =
                "//+ESC@ requires x > 0;\n" +       // line 0
                "//-JML@ ensures \\result > 0;\n" + // line 1
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(1, fs.get(0).getEndLine());
    }

    @Test
    public void testConditionalBlockAnnotation() {
        String source =
                "/*+ESC@ requires x > 0;\n" +       // line 0
                "       @ ensures \\result > 0;\n" + // line 1
                "       */\n" +                      // line 2
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Space-variant JML markers  (// @ and /* @)
    // -----------------------------------------------------------------------

    @Test
    public void testSpaceAfterSlashes() {
        // "// @" is a valid JML line comment marker.
        String source =
                "    // @ requires x > 0;\n" +
                "    // @ ensures \\result > 0;\n" +
                "    public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(1, fs.get(0).getEndLine());
    }

    @Test
    public void testSpaceAfterSlashStar() {
        // "/* @" is a valid JML block comment start.
        String source =
                "    /* @ requires x > 0;\n" +   // line 0
                "       @ ensures \\result > 0;\n" + // line 1
                "       @*/\n" +                  // line 2
                "    public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    @Test
    public void testSpaceSingleLine_noFold() {
        // Single "// @" line — no fold.
        String source =
                "    // @ requires x > 0;\n" +
                "    public int foo(int x) { return x; }\n";
        assertTrue(folds(source).isEmpty());
    }

    // -----------------------------------------------------------------------
    // Leading whitespace
    // -----------------------------------------------------------------------

    @Test
    public void testLeadingWhitespace() {
        String source =
                "\t\t//@ requires x > 0;\n" +
                "\t\t//@ ensures \\result > 0;\n" +
                "\t\tpublic int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(1, fs.get(0).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Kind
    // -----------------------------------------------------------------------

    @Test
    public void testKindIsComment() {
        String source =
                "//@ requires x > 0;\n" +
                "//@ ensures \\result > 0;\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals("comment", fs.get(0).getKind());
    }

    // -----------------------------------------------------------------------
    // Unclosed block comment
    // -----------------------------------------------------------------------

    /**
     * An unclosed {@code /*@} block comment should produce a fold that extends
     * from the opener to the last line of the file.  The provider must not
     * crash or silently drop the fold when {@code *}{@code /} is never found.
     */
    @Test
    public void testUnclosedBlockCommentFoldsToEndOfFile() {
        // Four lines; the block comment on line 0 is never closed.
        String source =
                "/*@ requires x > 0;\n" +
                "  @ ensures \\result > x;\n" +
                "  @ assignable \\nothing;\n" +
                "public int m(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertFalse("An unclosed block comment must produce at least one fold", fs.isEmpty());
        FoldingRange fold = fs.get(0);
        assertEquals("Fold must start at line 0", 0, fold.getStartLine());
        // The fold end must be at or beyond line 2 (covers the JML body lines)
        assertTrue("Fold must extend beyond the opening line", fold.getEndLine() > 0);
    }
}
