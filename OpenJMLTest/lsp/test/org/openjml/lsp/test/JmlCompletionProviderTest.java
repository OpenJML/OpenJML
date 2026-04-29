package org.openjml.lsp.test;

import org.eclipse.lsp4j.CompletionItem;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.junit.Test;
import org.openjml.lsp.JmlCompletionProvider;

import java.util.List;

import static org.junit.Assert.*;

/**
 * Unit tests for {@link JmlCompletionProvider}.
 *
 * <p>All methods under test are pure functions (no compiler invocation, no LSP
 * server required), so these tests run very quickly and need no server setup.
 */
public class JmlCompletionProviderTest {

    // -----------------------------------------------------------------------
    // isInJmlContext
    // -----------------------------------------------------------------------

    @Test
    public void testInContextSingleLine() {
        // cursor inside "//@ requires x > 0;" — definitely in JML
        assertTrue(JmlCompletionProvider.isInJmlContext(
                "//@ requires x > 0;\n", new Position(0, 15)));
    }

    @Test
    public void testInContextSingleLineWithSpaces() {
        // "// @ requires" — spaces between // and @ are allowed
        assertTrue(JmlCompletionProvider.isInJmlContext(
                "// @ requires x > 0;\n", new Position(0, 15)));
    }

    @Test
    public void testNotInContextPlainJava() {
        assertFalse(JmlCompletionProvider.isInJmlContext(
                "public class Foo { int x = 1; }\n", new Position(0, 20)));
    }

    @Test
    public void testNotInContextRegularComment() {
        // plain // comment without @
        assertFalse(JmlCompletionProvider.isInJmlContext(
                "// requires x > 0;\n", new Position(0, 10)));
    }

    @Test
    public void testInContextBlockComment() {
        // cursor on the second line of an open /*@ ... */ block
        String content = "/*@ requires x > 0;\n  @ ensures \\result >= 0;\n  @*/\n";
        assertTrue(JmlCompletionProvider.isInJmlContext(content, new Position(1, 15)));
    }

    @Test
    public void testNotInContextAfterBlockCommentClose() {
        // cursor is in Java code after the /*@ ... @*/ block is closed
        String content = "/*@ requires x > 0; @*/\npublic int m(int x) { return x; }\n";
        assertFalse(JmlCompletionProvider.isInJmlContext(content, new Position(1, 15)));
    }

    // -----------------------------------------------------------------------
    // wordBeforeCursor
    // -----------------------------------------------------------------------

    @Test
    public void testWordBeforeCursorPartialKeyword() {
        // "//@ req" — cursor at col 7 (after 'q')
        assertEquals("req",
                JmlCompletionProvider.wordBeforeCursor("//@ req", new Position(0, 7)));
    }

    @Test
    public void testWordBeforeCursorBackslash() {
        // "//@ \\res" — cursor at col 8 (after 's')
        assertEquals("\\res",
                JmlCompletionProvider.wordBeforeCursor("//@ \\res", new Position(0, 8)));
    }

    @Test
    public void testWordBeforeCursorEmpty() {
        // cursor right after the space: "//@ " — no partial word
        assertEquals("",
                JmlCompletionProvider.wordBeforeCursor("//@ ", new Position(0, 4)));
    }

    @Test
    public void testWordBeforeCursorFullWord() {
        // "//@ requires" — cursor at end, returns "requires"
        assertEquals("requires",
                JmlCompletionProvider.wordBeforeCursor("//@ requires", new Position(0, 12)));
    }

    // -----------------------------------------------------------------------
    // wordBeforeCursorRange
    // -----------------------------------------------------------------------

    @Test
    public void testWordBeforeCursorRangeBackslash() {
        // "//@ \\res" — backslash starts at col 4, cursor at col 8
        String content = "//@ \\res";
        Range range = JmlCompletionProvider.wordBeforeCursorRange(content, new Position(0, 8));
        assertEquals(0, range.getStart().getLine());
        assertEquals(4, range.getStart().getCharacter());
        assertEquals(0, range.getEnd().getLine());
        assertEquals(8, range.getEnd().getCharacter());
    }

    @Test
    public void testWordBeforeCursorRangeEmpty() {
        // cursor at a space — range is a zero-width point
        String content = "//@ ";
        Range range = JmlCompletionProvider.wordBeforeCursorRange(content, new Position(0, 4));
        assertEquals(range.getStart().getCharacter(), range.getEnd().getCharacter());
    }

    // -----------------------------------------------------------------------
    // complete
    // -----------------------------------------------------------------------

    @Test
    public void testCompleteReturnsKeywordsInJmlContext() {
        // Cursor after partial "req": only "req*" keywords must appear.
        List<CompletionItem> items =
                JmlCompletionProvider.complete("//@ req", new Position(0, 7));
        assertFalse("Expected keyword completions inside JML context", items.isEmpty());
        assertTrue("'requires' must be in completions",
                items.stream().anyMatch(i -> "requires".equals(i.getLabel())));
        assertFalse("'ensures' must NOT be in completions for prefix 'req'",
                items.stream().anyMatch(i -> "ensures".equals(i.getLabel())));
        assertTrue("All returned keywords must start with the prefix 'req'",
                items.stream().allMatch(i -> i.getLabel().startsWith("req")));
    }

    @Test
    public void testCompleteEmptyOutsideJmlContext() {
        List<CompletionItem> items =
                JmlCompletionProvider.complete("public class Foo {}", new Position(0, 10));
        assertTrue("Expected no completions outside JML context", items.isEmpty());
    }

    @Test
    public void testCompleteBackslashItemsIncludeResult() {
        // Cursor after "\\": backslash completions must include \result
        List<CompletionItem> items =
                JmlCompletionProvider.complete("//@ \\", new Position(0, 5));
        assertFalse("Expected backslash completions", items.isEmpty());
        assertTrue("\\result must be in backslash completions",
                items.stream().anyMatch(i -> "\\result".equals(i.getLabel())));
    }

    @Test
    public void testCompleteBackslashItemsAllHaveTextEdit() {
        // Every backslash completion must carry a TextEdit (so the editor replaces
        // the '\' + partial word rather than inserting after '\')
        List<CompletionItem> items =
                JmlCompletionProvider.complete("//@ \\res", new Position(0, 8));
        assertFalse("Expected backslash completions after '\\res'", items.isEmpty());
        assertTrue("All backslash items must carry a TextEdit",
                items.stream().allMatch(i -> i.getTextEdit() != null));
        assertTrue("All backslash items must start with the prefix '\\res'",
                items.stream().allMatch(i -> i.getLabel().startsWith("\\res")));
        assertFalse("'\\old' must NOT appear for prefix '\\res'",
                items.stream().anyMatch(i -> "\\old".equals(i.getLabel())));
    }

    @Test
    public void testCompleteKeywordsHaveKeywordKind() {
        List<CompletionItem> items =
                JmlCompletionProvider.complete("//@ req", new Position(0, 7));
        assertTrue("All completions must have Keyword kind",
                items.stream().allMatch(i ->
                        i.getKind() == org.eclipse.lsp4j.CompletionItemKind.Keyword));
    }
}
