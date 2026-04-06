package org.openjml.lsp.test;

import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.TextDocumentContentChangeEvent;
import org.junit.Test;
import org.openjml.lsp.IncrementalSyncApplier;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

/**
 * Unit tests for {@link IncrementalSyncApplier#apply}.
 *
 * <p>Tests cover:
 * <ul>
 *   <li>Degenerate inputs (null, empty)</li>
 *   <li>Single incremental change: insert, delete, replace</li>
 *   <li>Multi-change events applied in order</li>
 *   <li>Full-replacement ({@code range == null}) alone and mixed with incremental</li>
 *   <li>Out-of-bounds range fallback</li>
 *   <li>Multi-line content</li>
 *   <li>Common typing scenarios (single-char insert/delete)</li>
 * </ul>
 */
public class IncrementalSyncApplierTest {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Build a change event with a range. */
    private static TextDocumentContentChangeEvent inc(
            int startLine, int startChar, int endLine, int endChar, String text) {
        TextDocumentContentChangeEvent e = new TextDocumentContentChangeEvent();
        e.setRange(new Range(new Position(startLine, startChar),
                             new Position(endLine,   endChar)));
        e.setText(text);
        return e;
    }

    /** Build a full-document replacement event (no range). */
    private static TextDocumentContentChangeEvent full(String text) {
        TextDocumentContentChangeEvent e = new TextDocumentContentChangeEvent();
        // range intentionally left null — full replacement
        e.setText(text);
        return e;
    }

    private static String apply(String current,
                                TextDocumentContentChangeEvent... changes) {
        List<TextDocumentContentChangeEvent> list = new ArrayList<>();
        for (TextDocumentContentChangeEvent c : changes) list.add(c);
        return IncrementalSyncApplier.apply(current, list);
    }

    // -----------------------------------------------------------------------
    // Degenerate inputs
    // -----------------------------------------------------------------------

    @Test
    public void testNullCurrent_emptyChanges() {
        assertEquals("", IncrementalSyncApplier.apply(null, List.of()));
    }

    @Test
    public void testEmptyChanges_returnsOriginal() {
        assertEquals("hello", IncrementalSyncApplier.apply("hello", List.of()));
    }

    @Test
    public void testNullCurrent_fullReplacement() {
        assertEquals("new", apply(null, full("new")));
    }

    @Test
    public void testNullCurrent_incrementalInsertAtStart() {
        // Incremental into null/empty — insert "ab" at (0,0)..(0,0)
        assertEquals("ab", apply(null, inc(0, 0, 0, 0, "ab")));
    }

    // -----------------------------------------------------------------------
    // Full-document replacement
    // -----------------------------------------------------------------------

    @Test
    public void testSingleFullReplacement() {
        assertEquals("world", apply("hello", full("world")));
    }

    @Test
    public void testFullReplacement_nullText_becomesEmpty() {
        TextDocumentContentChangeEvent e = new TextDocumentContentChangeEvent();
        // range null, text null
        assertEquals("", IncrementalSyncApplier.apply("hello", List.of(e)));
    }

    @Test
    public void testMultipleFullReplacements_lastWins() {
        assertEquals("third", apply("first", full("second"), full("third")));
    }

    // -----------------------------------------------------------------------
    // Single incremental change
    // -----------------------------------------------------------------------

    @Test
    public void testInsertAtStart() {
        // "hello" → "XYhello"
        assertEquals("XYhello", apply("hello", inc(0, 0, 0, 0, "XY")));
    }

    @Test
    public void testInsertAtEnd() {
        // "hello" → "helloXY"
        assertEquals("helloXY", apply("hello", inc(0, 5, 0, 5, "XY")));
    }

    @Test
    public void testInsertInMiddle() {
        // "hello" → "heXYllo"
        assertEquals("heXYllo", apply("hello", inc(0, 2, 0, 2, "XY")));
    }

    @Test
    public void testDeleteFromStart() {
        // "hello" → "llo"  (delete chars 0..2)
        assertEquals("llo", apply("hello", inc(0, 0, 0, 2, "")));
    }

    @Test
    public void testDeleteFromEnd() {
        // "hello" → "hel"  (delete chars 3..5)
        assertEquals("hel", apply("hello", inc(0, 3, 0, 5, "")));
    }

    @Test
    public void testDeleteFromMiddle() {
        // "hello" → "hlo"  (delete chars 1..3, i.e. "el")
        assertEquals("hlo", apply("hello", inc(0, 1, 0, 3, "")));
    }

    @Test
    public void testReplaceMiddle() {
        // "hello" → "hXYo"  (replace chars 1..4 with "XY")
        assertEquals("hXYo", apply("hello", inc(0, 1, 0, 4, "XY")));
    }

    @Test
    public void testReplaceWholeContent() {
        // Incremental replacement of the entire single-line content
        assertEquals("world", apply("hello", inc(0, 0, 0, 5, "world")));
    }

    @Test
    public void testDeleteEntireContent() {
        assertEquals("", apply("hello", inc(0, 0, 0, 5, "")));
    }

    // -----------------------------------------------------------------------
    // Common typing scenario: single-character insert/delete
    // -----------------------------------------------------------------------

    @Test
    public void testSingleCharInsert() {
        // "ab" + insert 'c' at position 2 → "abc"
        assertEquals("abc", apply("ab", inc(0, 2, 0, 2, "c")));
    }

    @Test
    public void testSingleCharDelete_backspace() {
        // "abc" + delete char at position 2 → "ab"
        assertEquals("ab", apply("abc", inc(0, 2, 0, 3, "")));
    }

    @Test
    public void testSingleCharInsertIntoEmpty() {
        assertEquals("a", apply("", inc(0, 0, 0, 0, "a")));
    }

    // -----------------------------------------------------------------------
    // Multi-line content
    // -----------------------------------------------------------------------

    @Test
    public void testInsertOnSecondLine() {
        // "line0\nline1\n" → insert "X" at start of line 1
        String src = "line0\nline1\n";
        assertEquals("line0\nXline1\n", apply(src, inc(1, 0, 1, 0, "X")));
    }

    @Test
    public void testReplaceOnThirdLine() {
        String src = "aaa\nbbb\nccc\n";
        // Replace "ccc" on line 2 with "ZZZ"
        assertEquals("aaa\nbbb\nZZZ\n", apply(src, inc(2, 0, 2, 3, "ZZZ")));
    }

    @Test
    public void testDeleteCrossLineContent() {
        // "abc\ndef\n" — delete from (0,1) to (1,2) inclusive: deletes "bc\nde"
        // result: "af\n"
        String src = "abc\ndef\n";
        assertEquals("af\n", apply(src, inc(0, 1, 1, 2, "")));
    }

    @Test
    public void testInsertNewline() {
        // "ab" → "a\nb"
        assertEquals("a\nb", apply("ab", inc(0, 1, 0, 1, "\n")));
    }

    @Test
    public void testInsertNewlineThenInsertOnNewLine() {
        // Two sequential changes:
        // 1. "ab" → "a\nb"  (insert newline after 'a')
        // 2. On the new line 1 char 0, insert "X" → "a\nXb"
        assertEquals("a\nXb",
                apply("ab",
                      inc(0, 1, 0, 1, "\n"),
                      inc(1, 0, 1, 0, "X")));
    }

    // -----------------------------------------------------------------------
    // Multiple sequential incremental changes
    // -----------------------------------------------------------------------

    @Test
    public void testTwoChanges_secondAtHigherOffset() {
        // "hello world" — two changes applied in sequence:
        // 1. Insert "!" at end (0,11)→(0,11): "hello world!"
        // 2. Insert " " at (0,5)→(0,5) in the ALREADY MODIFIED string: "hello  world!"
        //    Wait — LSP says change 2 refers to state AFTER change 1.
        //    State after change 1: "hello world!" (length 12)
        //    Insert " " at (0,5)→(0,5): "hello  world!"
        assertEquals("hello  world!",
                apply("hello world",
                      inc(0, 11, 0, 11, "!"),
                      inc(0, 5,  0, 5,  " ")));
    }

    @Test
    public void testTwoChanges_bothAtSamePosition() {
        // Change 1: insert "A" at (0,3) in "hello" → "helAlo"
        // Change 2: insert "B" at (0,4) in "helAlo" → "helABlo"
        assertEquals("helABlo",
                apply("hello",
                      inc(0, 3, 0, 3, "A"),
                      inc(0, 4, 0, 4, "B")));
    }

    @Test
    public void testTwoChanges_deletesThenInsert() {
        // "hello" → delete 'e' at (0,1): "hllo"
        //         → insert 'a' at (0,1): "hallo"
        assertEquals("hallo",
                apply("hello",
                      inc(0, 1, 0, 2, ""),
                      inc(0, 1, 0, 1, "a")));
    }

    @Test
    public void testThreeChanges_sequentialTyping() {
        // Simulate typing "cat" one char at a time into ""
        assertEquals("cat",
                apply("",
                      inc(0, 0, 0, 0, "c"),
                      inc(0, 1, 0, 1, "a"),
                      inc(0, 2, 0, 2, "t")));
    }

    // -----------------------------------------------------------------------
    // Full replacement mixed with incremental
    // -----------------------------------------------------------------------

    @Test
    public void testFullReplacementFollowedByIncremental() {
        // Full replacement "world" then insert "!" at end.
        assertEquals("world!",
                apply("hello",
                      full("world"),
                      inc(0, 5, 0, 5, "!")));
    }

    @Test
    public void testIncrementalFollowedByFullReplacement() {
        // Incremental change first, then full replacement — full wins.
        assertEquals("final",
                apply("hello",
                      inc(0, 0, 0, 5, "ignored"),
                      full("final")));
    }

    @Test
    public void testFullReplacementInMiddle_discardsBefore() {
        // Three changes: inc, full, inc.
        // The full replacement at index 1 discards the original + change 0.
        // Change 2 (incremental) applies to the result of the full replacement.
        assertEquals("baseX",
                apply("original",
                      inc(0, 0, 0, 8, "ignored"),   // discarded by full below
                      full("base"),
                      inc(0, 4, 0, 4, "X")));
    }

    @Test
    public void testLastOfMultipleFullReplacementsWins() {
        assertEquals("last",
                apply("start",
                      full("first"),
                      full("second"),
                      full("last")));
    }

    @Test
    public void testAllFullReplacementsNoIncremental() {
        // No incremental changes after the last full-replacement → return immediately.
        assertEquals("only", apply("prev", full("only")));
    }

    // -----------------------------------------------------------------------
    // Out-of-bounds range fallback
    // -----------------------------------------------------------------------

    @Test
    public void testOutOfBounds_startBeyondEnd_fallsBackToFullText() {
        // Range start > end is invalid; the change text is used as a full replacement.
        // startChar=10 > endChar=5 for a 5-char string.
        assertEquals("fallback",
                apply("hello", inc(0, 10, 0, 5, "fallback")));
    }

    @Test
    public void testOutOfBounds_lineBeyondContent_appendsAtEnd() {
        // lineColToOffset clamps an out-of-range line to end-of-file, so
        // start == end == content.length() — a valid zero-width insert at the end.
        assertEquals("hellofallback",
                apply("hello", inc(5, 0, 5, 0, "fallback")));
    }

    @Test
    public void testOutOfBounds_startAfterEnd_fallsBackToFullText() {
        // start (col 10) > end (col 5) is structurally invalid — the applier
        // treats the change text as a full-document replacement.
        assertEquals("fallback",
                apply("hello", inc(0, 10, 0, 5, "fallback")));
    }

    @Test
    public void testOutOfBounds_fallbackFollowedByIncremental() {
        // After an invalid-range fallback to "fallback", the subsequent
        // incremental change applies to "fallback".
        assertEquals("fallbackX",
                apply("hello",
                      inc(0, 10, 0, 5, "fallback"),  // invalid range → full replacement
                      inc(0, 8, 0, 8, "X")));
    }
}
