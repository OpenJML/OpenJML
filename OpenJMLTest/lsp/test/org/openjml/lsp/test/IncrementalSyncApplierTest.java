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
 * Correctness tests for {@link IncrementalSyncApplier#apply}.
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
 *
 * <p>Timing and transmission-cost benchmarks live in {@link SyncTimingTests},
 * which is intentionally excluded from the normal test suite.
 */
public class IncrementalSyncApplierTest {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Build a change event with a range. */
    static TextDocumentContentChangeEvent inc(
            int startLine, int startChar, int endLine, int endChar, String text) {
        TextDocumentContentChangeEvent e = new TextDocumentContentChangeEvent();
        e.setRange(new Range(new Position(startLine, startChar),
                             new Position(endLine,   endChar)));
        e.setText(text);
        return e;
    }

    /** Build a full-document replacement event (no range). */
    static TextDocumentContentChangeEvent full(String text) {
        TextDocumentContentChangeEvent e = new TextDocumentContentChangeEvent();
        // range intentionally left null — full replacement
        e.setText(text);
        return e;
    }

    static String apply(String current,
                        TextDocumentContentChangeEvent... changes) {
        List<TextDocumentContentChangeEvent> list = new ArrayList<>();
        for (TextDocumentContentChangeEvent c : changes) list.add(c);
        return IncrementalSyncApplier.apply(current, list);
    }

    // -----------------------------------------------------------------------
    // Degenerate inputs
    // -----------------------------------------------------------------------

    @Test
    public void testNullCurrentTreatedAsEmpty() {
        assertEquals("hello", apply(null, inc(0, 0, 0, 0, "hello")));
    }

    @Test
    public void testNullChangeListReturnsOriginal() {
        assertEquals("hello", IncrementalSyncApplier.apply("hello", null));
    }

    @Test
    public void testEmptyChangeListReturnsOriginal() {
        assertEquals("hello", IncrementalSyncApplier.apply("hello", List.of()));
    }

    @Test
    public void testInsertIntoEmptyDocument() {
        assertEquals("hello", apply("", inc(0, 0, 0, 0, "hello")));
    }

    // -----------------------------------------------------------------------
    // Single incremental change
    // -----------------------------------------------------------------------

    @Test
    public void testInsertAtStart() {
        assertEquals("XYZhello", apply("hello", inc(0, 0, 0, 0, "XYZ")));
    }

    @Test
    public void testInsertAtEnd() {
        assertEquals("helloXYZ", apply("hello", inc(0, 5, 0, 5, "XYZ")));
    }

    @Test
    public void testInsertAtMiddle() {
        assertEquals("heXYZllo", apply("hello", inc(0, 2, 0, 2, "XYZ")));
    }

    @Test
    public void testDeleteFromStart() {
        assertEquals("llo", apply("hello", inc(0, 0, 0, 2, "")));
    }

    @Test
    public void testDeleteFromEnd() {
        assertEquals("hel", apply("hello", inc(0, 3, 0, 5, "")));
    }

    @Test
    public void testDeleteFromMiddle() {
        assertEquals("hlo", apply("hello", inc(0, 1, 0, 3, "")));
    }

    @Test
    public void testReplaceEntireString() {
        assertEquals("world", apply("hello", inc(0, 0, 0, 5, "world")));
    }

    @Test
    public void testReplacePartialString() {
        // Replace chars 1..3 ("ell") with "XYZ" → "hXYZo"
        assertEquals("hXYZo", apply("hello", inc(0, 1, 0, 4, "XYZ")));
    }

    @Test
    public void testInsertNewlineCreatesSecondLine() {
        assertEquals("hel\nlo", apply("hello", inc(0, 3, 0, 3, "\n")));
    }

    @Test
    public void testDeleteNewlineMergesLines() {
        assertEquals("hello", apply("hel\nlo", inc(0, 3, 1, 0, "")));
    }

    // -----------------------------------------------------------------------
    // Multi-change events (applied in the order given)
    // -----------------------------------------------------------------------

    @Test
    public void testTwoInsertsInOrder() {
        // Insert "A" at col 0, then "B" at col 2 of the updated string "Ahello"
        assertEquals("ABhello",
                apply("hello",
                      inc(0, 0, 0, 0, "A"),
                      inc(0, 1, 0, 1, "B")));
    }

    @Test
    public void testInsertThenDelete() {
        // Insert "XYZ" at start → "XYZhello", then delete first 3 → "hello"
        assertEquals("hello",
                apply("hello",
                      inc(0, 0, 0, 0, "XYZ"),
                      inc(0, 0, 0, 3, "")));
    }

    @Test
    public void testDeleteThenInsert() {
        // Delete "hel" → "lo", then insert "HEL" at start → "HELlo"
        assertEquals("HELlo",
                apply("hello",
                      inc(0, 0, 0, 3, ""),
                      inc(0, 0, 0, 0, "HEL")));
    }

    @Test
    public void testThreeConsecutiveInserts() {
        assertEquals("ABChello",
                apply("hello",
                      inc(0, 0, 0, 0, "A"),
                      inc(0, 1, 0, 1, "B"),
                      inc(0, 2, 0, 2, "C")));
    }

    // -----------------------------------------------------------------------
    // Multi-line content
    // -----------------------------------------------------------------------

    @Test
    public void testInsertOnSecondLine() {
        assertEquals("line1\nliXne2\n",
                apply("line1\nline2\n", inc(1, 2, 1, 2, "X")));
    }

    @Test
    public void testDeleteAcrossLines() {
        assertEquals("line1\nne2\n",
                apply("line1\nline2\n", inc(1, 0, 1, 2, "")));
    }

    @Test
    public void testReplaceAcrossLines() {
        // Range (0,4)→(1,4) covers "1\nline" (offset 4 through 10); replace with "X".
        assertEquals("lineX2\n",
                apply("line1\nline2\n",
                      inc(0, 4, 1, 4, "X")));
    }

    @Test
    public void testInsertNewLineInMiddle() {
        assertEquals("line1\nnewline\nline2\n",
                apply("line1\nline2\n", inc(1, 0, 1, 0, "newline\n")));
    }

    @Test
    public void testMultiLineMultipleChanges() {
        String doc = "aaa\nbbb\nccc\n";
        // Insert "X" at start of line 1, then "Y" at start of line 2 of result
        assertEquals("aaa\nXbbb\nYccc\n",
                apply(doc,
                      inc(1, 0, 1, 0, "X"),
                      inc(2, 0, 2, 0, "Y")));
    }

    // -----------------------------------------------------------------------
    // Full-replacement (range == null)
    // -----------------------------------------------------------------------

    @Test
    public void testFullReplacementAlone() {
        assertEquals("newcontent", apply("old", full("newcontent")));
    }

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
