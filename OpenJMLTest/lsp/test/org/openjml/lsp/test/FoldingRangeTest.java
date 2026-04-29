package org.openjml.lsp.test;

import org.eclipse.lsp4j.FoldingRange;
import org.junit.Test;
import org.openjml.lsp.FoldingRangeProvider;

import java.util.List;

import static org.junit.Assert.*;

/**
 * Tests for {@link FoldingRangeProvider}: textDocument/foldingRange.
 *
 * <p>Pure text scan -- no AST or CheckRunner needed.
 *
 * <h3>Rules under test</h3>
 * <ul>
 *   <li>A fold starts on a line that ends with a JML comment (JML line comment,
 *       unterminated JML block, or terminated JML block followed only by
 *       whitespace/Java comments).</li>
 *   <li>A fold continues through consecutive JML comments, Java line/block
 *       comments, and whitespace -- but NOT through blank lines outside a block
 *       comment, and NOT through lines with non-comment program text.</li>
 *   <li>Java comments alone do NOT start a fold; they only extend one.</li>
 *   <li>Blank lines inside a block comment (JML or Java) do NOT terminate.</li>
 *   <li>Only folds of two or more lines are emitted.</li>
 * </ul>
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

    @Test
    public void testJavaOnlyComments_noFold() {
        // Java comments alone do NOT start a fold.
        String source =
                "// A plain Java comment\n" +
                "// another Java comment\n" +
                "public int foo() { return 0; }\n";
        assertTrue(folds(source).isEmpty());
    }

    // -----------------------------------------------------------------------
    // JML line comments
    // -----------------------------------------------------------------------

    @Test
    public void testTwoConsecutiveLineComments() {
        String source =
                "    //@ requires x > 0;\n" +      // line 0
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
                "public int foo(int x) { return x; }\n" + // line 2 -- breaks group
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
    // JML block comments
    // -----------------------------------------------------------------------

    @Test
    public void testSingleLineBlockComment_noFold() {
        // A terminated single-line JML block comment does not produce a fold.
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
    // Mixed JML and Java comments in the same region
    // -----------------------------------------------------------------------

    @Test
    public void testMixedLineAndBlock() {
        // JML block (lines 0-1) followed immediately by a JML line comment (line 2).
        String source =
                "/*@ requires x > 0;\n" +           // line 0 -- block start
                "  @ ensures \\result > 0; */\n" +  // line 1 -- block end
                "//@ assignable \\nothing;\n" +      // line 2 -- extends region
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    @Test
    public void testJavaLineCommentContinuesFold() {
        // A Java line comment between two JML line comments extends the fold.
        String source =
                "//@ requires x > 0;\n" +           // line 0 -- JML, starts fold
                "// see also the spec file\n" +      // line 1 -- Java line comment
                "//@ ensures \\result > 0;\n" +      // line 2 -- JML, extends fold
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    @Test
    public void testJavaLineCommentAtEndOfFold() {
        // A Java line comment at the end extends the fold to include it.
        String source =
                "//@ requires x > 0;\n" +           // line 0
                "//@ ensures \\result > 0;\n" +      // line 1
                "// end of JML block\n" +            // line 2 -- Java, extends fold
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    @Test
    public void testJavaBlockCommentContinuesFold() {
        // A multi-line Java block comment between JML lines extends the fold.
        String source =
                "//@ requires x > 0;\n" +           // line 0 -- starts fold
                "/* implementation note\n" +         // line 1 -- Java block start
                "   spans two lines */\n" +          // line 2 -- Java block end
                "//@ ensures \\result > 0;\n" +      // line 3 -- extends fold
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(3, fs.get(0).getEndLine());
    }

    @Test
    public void testSingleLineJavaBlockCommentContinuesFold() {
        // A terminated single-line Java block comment extends an active fold.
        String source =
                "//@ requires x > 0;\n" +           // line 0
                "/* brief note */\n" +               // line 1 -- Java block, extends fold
                "//@ ensures \\result > 0;\n" +      // line 2
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Blank lines
    // -----------------------------------------------------------------------

    @Test
    public void testBlankLineTerminatesFold() {
        // A blank line outside a block comment breaks the fold.
        // Each resulting JML group has only one line, so no fold is emitted.
        String source =
                "//@ requires x > 0;\n" +           // line 0
                "\n" +                               // line 1 -- blank: terminates
                "//@ ensures \\result > 0;\n" +      // line 2
                "public int foo(int x) { return x; }\n";
        assertTrue(folds(source).isEmpty());
    }

    @Test
    public void testBlankLineInsideJmlBlockDoesNotTerminate() {
        // A blank line that falls inside a JML block comment is part of the
        // block and must NOT terminate the fold.
        String source =
                "/*@ requires x > 0;\n" +           // line 0 -- block start
                "\n" +                               // line 1 -- blank inside block
                "  @ ensures \\result > 0;\n" +      // line 2
                "  @*/\n" +                          // line 3 -- block end
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(3, fs.get(0).getEndLine());
    }

    @Test
    public void testBlankLineInsideJavaBlockDoesNotTerminate() {
        // A blank line inside a Java block comment (part of an active fold)
        // must NOT terminate the fold.
        String source =
                "//@ requires x > 0;\n" +           // line 0 -- starts fold
                "/* note:\n" +                       // line 1 -- Java block start
                "\n" +                               // line 2 -- blank inside block
                "   detail */\n" +                   // line 3 -- Java block end
                "//@ ensures \\result > 0;\n" +      // line 4 -- extends fold
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(4, fs.get(0).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Program text after block-comment close
    // -----------------------------------------------------------------------

    @Test
    public void testProgramTextAfterBlockCloseTerminatesFold() {
        // When "*/" is followed by program text on the same line, the fold
        // terminates without including that line.
        String source =
                "//@ requires x > 0;\n" +           // line 0 -- starts fold
                "/* note */ int y = 0;\n" +          // line 1 -- Java block, then program text
                "public int foo(int x) { return x; }\n";
        // fold(0,0) -- single line, not emitted
        assertTrue(folds(source).isEmpty());
    }

    @Test
    public void testProgramTextAfterJmlBlockCloseTerminatesFold() {
        // Same as above but with a JML block comment.
        String source =
                "/*@ spec */ int x = 0;\n" +        // line 0 -- JML block, then program text
                "int y = 0;\n";
        assertTrue(folds(source).isEmpty());
    }

    @Test
    public void testJmlBlockWithProgramTextSplitsRegion() {
        // A "/*@ ... */ programtext" line ends the preceding JML region (without
        // including that line in its endLine).  The outer scan resumes from the
        // program text, so the next fold starts on the following JML line (line 3).
        String source =
                "    //@ // asd\n" +                       // line 0
                "    //@ // asd\n" +                       // line 1
                "    /*@ ghost int z; */ int g;\n" +       // line 2 -- JML + program text
                "    //@ // asd\n" +                       // line 3
                "    //@ // asd\n" +                       // line 4
                "    //@ // asd\n";                        // line 5
        List<FoldingRange> fs = folds(source);
        assertEquals(2, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(1, fs.get(0).getEndLine());
        assertEquals(3, fs.get(1).getStartLine());
        assertEquals(5, fs.get(1).getEndLine());
    }

    @Test
    public void testProgramTextBeforeJmlBlockStartsRegion() {
        // A line that begins with program text but contains a "/*@" mid-line starts
        // a folding region; the block comment continues on the next line.
        String source =
                "    public int i; /*@ // asd\n" +   // line 0 -- program text, then JML block
                "    */ // asd\n" +                  // line 1 -- closes block
                "    //@ // sdf\n";                  // line 2 -- extends region
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Blank lines separating two multi-line groups (each group produces a fold)
    // -----------------------------------------------------------------------

    @Test
    public void testBlankLineSeparatesTwoMultiLineFolds() {
        // A blank line terminates the first fold; a second multi-line group produces
        // a second independent fold.
        String source =
                "//@ requires x > 0;\n" +           // line 0
                "//@ ensures \\result > 0;\n" +      // line 1
                "\n" +                               // line 2 -- blank: terminates first fold
                "//@ requires y > 0;\n" +            // line 3
                "//@ ensures \\result >= 0;\n" +     // line 4
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(2, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(1, fs.get(0).getEndLine());
        assertEquals(3, fs.get(1).getStartLine());
        assertEquals(4, fs.get(1).getEndLine());
    }

    @Test
    public void testMultipleBlankLinesSeparatesGroups() {
        // Multiple consecutive blank lines between groups: same result as one blank line.
        String source =
                "//@ requires x > 0;\n" +           // line 0
                "//@ ensures \\result > 0;\n" +      // line 1
                "\n" +                               // line 2
                "\n" +                               // line 3
                "//@ requires y > 0;\n" +            // line 4
                "//@ ensures \\result >= 0;\n" +     // line 5
                "public int bar(int y) { return y; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(2, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(1, fs.get(0).getEndLine());
        assertEquals(4, fs.get(1).getStartLine());
        assertEquals(5, fs.get(1).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Multiple block comments on the same extension line
    // -----------------------------------------------------------------------

    @Test
    public void testTwoAdjacentBlockCommentsOnExtensionLine() {
        // Two adjacent single-line block comments on one line both extend the fold;
        // the line is not a blank line, so the fold continues after them.
        String source =
                "//@ requires x > 0;\n" +           // line 0 -- starts fold
                "/* note1 */ /* note2 */\n" +        // line 1 -- two Java blocks, extend fold
                "//@ ensures \\result > 0;\n" +      // line 2 -- extends fold
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Program text on non-first extension lines
    // -----------------------------------------------------------------------

    @Test
    public void testProgramTextOnExtensionLineTerminatesFold() {
        // A non-comment token before a comment on an extension line terminates
        // the fold (the line's comment is not included).
        String source =
                "//@ requires x > 0;\n" +           // line 0
                "//@ ensures \\result > 0;\n" +      // line 1
                "int x = foo(); // side effect\n" +  // line 2 -- program text first: stops fold
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(1, fs.get(0).getEndLine());
    }

    @Test
    public void testProgramTextBetweenBlockCommentsOnExtensionLineTerminatesFold() {
        // On an extension line, program text between two block comments terminates
        // the fold after absorbing the first block comment; the second is not included.
        String source =
                "//@ requires x > 0;\n" +           // line 0
                "/* n1 */ int x = 0; /* n2 */\n" +  // line 1 -- program text after n1
                "public int foo(int x) { return x; }\n";
        // fold(0,0) -- single line, not emitted
        assertTrue(folds(source).isEmpty());
    }

    // -----------------------------------------------------------------------
    // Java block comment outside any active region
    // -----------------------------------------------------------------------

    @Test
    public void testJmlInsideJavaBlockNotMisclassified() {
        // Text inside a Java block comment that looks like a JML annotation
        // must NOT start a fold -- it is part of the Java comment.
        String source =
                "/* Java block:\n" +                 // line 0 -- Java block, no active region
                "   //@ not real JML\n" +            // line 1 -- inside Java block
                "*/\n" +                             // line 2 -- block end
                "//@ real JML requires x > 0;\n" +  // line 3 -- starts fold
                "//@ real JML ensures true;\n" +     // line 4
                "public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(3, fs.get(0).getStartLine());
        assertEquals(4, fs.get(0).getEndLine());
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
                "/*+ESC@ requires x > 0;\n" +        // line 0
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
                "    /* @ requires x > 0;\n" +       // line 0
                "       @ ensures \\result > 0;\n" + // line 1
                "       @*/\n" +                     // line 2
                "    public int foo(int x) { return x; }\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    @Test
    public void testSpaceSingleLine_noFold() {
        // Single "// @" line -- no fold.
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
    // Text blocks
    // -----------------------------------------------------------------------

    @Test
    public void testTextBlockProducesFold() {
        // A multi-line text block is foldable.
        String source =
                "String s = \"\"\"\n" +       // line 0 -- opening """
                "    hello\n" +              // line 1 -- content
                "    world\n" +              // line 2 -- content
                "    \"\"\";\n" +            // line 3 -- closing """
                "int x = 0;\n";
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(3, fs.get(0).getEndLine());
    }

    @Test
    public void testTextBlockAndJmlAreIndependentFolds() {
        // A text block and a JML block produce two independent folds.
        String source =
                "String s = \"\"\"\n" +       // line 0 -- text block
                "    hello\n" +              // line 1
                "    \"\"\";\n" +            // line 2 -- closing """
                "//@ requires x > 0;\n" +   // line 3 -- JML (starts second fold)
                "//@ ensures true;\n";       // line 4
        List<FoldingRange> fs = folds(source);
        assertEquals(2, fs.size());
        assertEquals(0, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
        assertEquals(3, fs.get(1).getStartLine());
        assertEquals(4, fs.get(1).getEndLine());
    }

    // -----------------------------------------------------------------------
    // String and character literals (must not confuse the scanner)
    // -----------------------------------------------------------------------

    @Test
    public void testJmlInsideStringLiteralNotMisclassified() {
        // A JML-like token inside a string literal must NOT start a fold.
        String source =
                "String s = \"//@requires x > 0;\";\n" +  // line 0 -- string, not JML
                "//@ requires x > 0;\n" +                  // line 1 -- real JML
                "//@ ensures true;\n";                      // line 2
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(1, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    @Test
    public void testJmlInsideCharLiteralNotMisclassified() {
        // A slash inside a char literal must not trigger comment detection.
        String source =
                "char c = '/';\n" +           // line 0 -- char literal
                "//@ requires x > 0;\n" +     // line 1
                "//@ ensures true;\n";         // line 2
        List<FoldingRange> fs = folds(source);
        assertEquals(1, fs.size());
        assertEquals(1, fs.get(0).getStartLine());
        assertEquals(2, fs.get(0).getEndLine());
    }

    // -----------------------------------------------------------------------
    // Unclosed block comment
    // -----------------------------------------------------------------------

    /**
     * An unclosed {@code /*@} block comment should produce a fold that extends
     * to the last line of the file.  The provider must not crash or silently
     * drop the fold when {@code *}{@code /} is never found.
     */
    @Test
    public void testUnclosedBlockCommentFoldsToEndOfFile() {
        String source =
                "/*@ requires x > 0;\n" +           // line 0 -- block never closed
                "  @ ensures \\result > x;\n" +     // line 1
                "  @ assignable \\nothing;\n" +     // line 2
                "public int m(int x) { return x; }\n"; // line 3
        List<FoldingRange> fs = folds(source);
        assertFalse("Unclosed block comment must produce a fold", fs.isEmpty());
        assertEquals(0, fs.get(0).getStartLine());
        assertTrue("Fold must extend past the opening line",
                fs.get(0).getEndLine() > 0);
    }
}
