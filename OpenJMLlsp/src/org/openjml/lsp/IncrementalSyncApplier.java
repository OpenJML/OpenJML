package org.openjml.lsp;

import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.TextDocumentContentChangeEvent;

import java.util.List;

/**
 * Applies a list of LSP {@code textDocument/didChange} incremental change
 * events to a document string, producing the updated string.
 *
 * <p>Changes must be applied strictly in the order given: each change's
 * {@code range} refers to the document state <em>after</em> all preceding
 * changes in the same event have been applied.  Reordering changes (e.g. by
 * sort) would corrupt the result for overlapping or adjacent ranges.
 *
 * <p>Algorithm:
 * <ol>
 *   <li>Scan backward to find the last full-document replacement
 *       ({@code range == null}).  Everything before it is discarded; it
 *       becomes the new baseline {@code current}.  All changes after it are
 *       guaranteed to be incremental.</li>
 *   <li>Compute a conservative upper-bound capacity for the {@link StringBuilder}:
 *       {@code current.length() + sum of all remaining newText lengths}.
 *       This overestimates by the amount of deleted text, but guarantees the
 *       builder never needs to resize (no internal copy).</li>
 *   <li>Apply incremental changes in order:
 *       <ul>
 *         <li>First change: three-part copy (prefix, newText, suffix) into
 *             the pre-sized builder — a single O(n) pass.</li>
 *         <li>Subsequent changes: {@link StringBuilder#replace} in place —
 *             no intermediate {@link String} per change.</li>
 *       </ul></li>
 * </ol>
 *
 * <p>Memory notes: {@code StringBuilder.append(String, start, end)} copies
 * directly from the source {@code String}'s backing array without creating a
 * substring.  The single {@link StringBuilder#toString()} call at the end
 * produces the final immutable {@link String}.  For the common single-change
 * case there is exactly one allocation (the builder) and one final copy.
 */
public final class IncrementalSyncApplier {

    private IncrementalSyncApplier() {}

    /**
     * Apply {@code changes} to {@code current} and return the updated string.
     *
     * @param current the document content before this batch of changes;
     *                {@code null} is treated as an empty string
     * @param changes the ordered list from
     *                {@link org.eclipse.lsp4j.DidChangeTextDocumentParams#getContentChanges()}
     * @return the new document content; {@code current} (unchanged) if
     *         {@code changes} is empty
     */
    public static String apply(String current,
                               List<TextDocumentContentChangeEvent> changes) {
        if (current == null) current = "";
        if (changes == null || changes.isEmpty()) return current;

        // --- Phase 1: find the last full-replacement (range == null) ---
        // Everything before it, including the original content, is discarded.
        // After this loop, all remaining changes (firstIdx..end) have range != null.
        int firstIdx = 0;
        for (int i = changes.size() - 1; i >= 0; i--) {
            if (changes.get(i).getRange() == null) {
                String t = changes.get(i).getText();
                current = (t != null) ? t : "";
                firstIdx = i + 1;
                break;
            }
        }
        // If all changes were full-replacements the last one is already in current.
        if (firstIdx == changes.size()) return current;

        // Log when a single event carries multiple incremental changes — this is
        // unusual in practice (most editors send one change per keystroke) and helps
        // detect whether clients are batching edits in ways that exercise the
        // multi-change sb.replace() path.
        int numIncremental = changes.size() - firstIdx;
        if (numIncremental > 1) {
            System.err.println("[IncrementalSyncApplier] " + numIncremental
                    + " incremental changes in one didChange event");
        }

        // --- Phase 2: compute conservative capacity ---
        // current.length() + sum(newText.length()) never requires a resize,
        // because deletions only shrink and this adds all insertion lengths.
        int capacity = current.length();
        for (int i = firstIdx; i < changes.size(); i++) {
            String t = changes.get(i).getText();
            if (t != null) capacity += t.length();
        }

        // --- Phase 3: apply incremental changes in order ---
        StringBuilder sb = null;

        for (int i = firstIdx; i < changes.size(); i++) {
            TextDocumentContentChangeEvent change = changes.get(i);
            String newText = change.getText() != null ? change.getText() : "";
            Range  range   = change.getRange();          // guaranteed non-null by Phase 1

            // Resolve (line,col) ranges against the current content snapshot.
            // For i == firstIdx  the snapshot is the original String (no extra copy).
            // For i > firstIdx   we need sb.toString() — O(n), but multi-change
            // events are rare and this is still cheaper than a full-document sync.
            String snapshot = (sb == null) ? current : sb.toString();

            int start = DefinitionFinder.lineColToOffset(
                    snapshot,
                    range.getStart().getLine(),
                    range.getStart().getCharacter());
            int end = DefinitionFinder.lineColToOffset(
                    snapshot,
                    range.getEnd().getLine(),
                    range.getEnd().getCharacter());

            if (start < 0 || end < 0 || start > end || end > snapshot.length()) {
                // Out-of-bounds range — treat the new text as a full replacement
                // and continue applying subsequent changes on top of it.
                current = newText;
                sb = null;
                capacity = current.length();
                // Re-sum remaining insertions for the new capacity.
                for (int j = i + 1; j < changes.size(); j++) {
                    String t = changes.get(j).getText();
                    if (t != null) capacity += t.length();
                }
                continue;
            }

            if (sb == null) {
                // First incremental change: three-part copy into pre-sized builder.
                // append(String, start, end) reads directly from the String's char
                // array — no substring allocation.
                sb = new StringBuilder(capacity);
                sb.append(snapshot, 0, start);
                sb.append(newText);
                sb.append(snapshot, end, snapshot.length());
            } else {
                // Subsequent changes: in-place replace inside the builder.
                sb.replace(start, end, newText);
            }
        }

        return (sb != null) ? sb.toString() : current;
    }
}
