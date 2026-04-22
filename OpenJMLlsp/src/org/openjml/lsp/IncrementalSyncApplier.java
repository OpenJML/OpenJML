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
 * <h3>Algorithm</h3>
 * <ol>
 *   <li><b>Phase 1 — skip obsolete history.</b>  Scan backward to find the
 *       last full-document replacement ({@code range == null}).  Everything
 *       before it, including the original content, is discarded; it becomes
 *       the new baseline {@code current}.  All remaining changes are
 *       guaranteed to be incremental.</li>
 *   <li><b>Phase 2 — size the buffer.</b>  Compute a conservative upper-bound
 *       capacity: {@code current.length() + sum of all remaining newText
 *       lengths}.  This overestimates by the amount of deleted text but
 *       guarantees the {@link StringBuilder} never needs to resize.</li>
 *   <li><b>Phase 3 — apply changes.</b>  A single
 *       {@link DefinitionFinder.LineIndex} is created for {@code current} and
 *       kept alive across all changes:
 *       <ul>
 *         <li><em>First change:</em> three-part copy (prefix, newText, suffix)
 *             into the pre-sized builder using
 *             {@code append(String, start, end)} — reads directly from the
 *             {@code String}'s backing array, no substring allocation.  The
 *             index is then rebound to the builder via
 *             {@link DefinitionFinder.LineIndex#rebind}.</li>
 *         <li><em>Subsequent changes:</em> {@link StringBuilder#replace} in
 *             place.  After each edit,
 *             {@link DefinitionFinder.LineIndex#applyEdit} truncates the
 *             cached line-start array so that entries at or after the edit
 *             point are lazily recomputed from the updated builder — no
 *             {@code sb.toString()} snapshot is needed between changes.</li>
 *       </ul></li>
 * </ol>
 *
 * <h3>Performance notes</h3>
 * <p>The dominant cost is the {@code (line, col) → offset} conversion required
 * by the LSP range format.  {@link DefinitionFinder.LineIndex} amortises this
 * by caching line-start offsets and using {@code String.indexOf('\n', from)}
 * (JVM-intrinsified via SIMD) rather than a char-by-char scan.  Sharing one
 * index across the start and end of each range halves the number of scans; for
 * multi-delta events the rebound index eliminates redundant re-scanning of the
 * document prefix.  Benchmarks show incremental reconstruction is ~20–30%
 * faster than naive substring concatenation at 100K–1M characters.
 *
 * <p>The larger saving is on the wire: the JSON payload for a full-sync 1M-char
 * document is ~1 MB; an incremental payload is ~160 bytes regardless of size.
 * Gson serialisation of a 1M full-sync event costs ~2 ms versus ~2 µs for
 * incremental — a 1000x difference.  See {@code SyncTimingTests} for measured
 * data.
 *
 * <p>The {@code incrementalSync} flag in {@link OpenJMLSettings} allows
 * switching back to full-document sync if needed for debugging.
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
            ServerLog.serverLog("[IncrementalSyncApplier] " + numIncremental
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
        // One LineIndex is created for 'current' and kept alive across all
        // changes.  After each edit the index is updated via applyEdit() and,
        // after the first change, rebound to the StringBuilder so subsequent
        // toOffset() calls scan the builder directly — no sb.toString() needed
        // between changes in a multi-delta event.
        StringBuilder sb  = null;
        DefinitionFinder.LineIndex idx = new DefinitionFinder.LineIndex(current);

        for (int i = firstIdx; i < changes.size(); i++) {
            TextDocumentContentChangeEvent change = changes.get(i);
            String newText   = change.getText() != null ? change.getText() : "";
            Range  range     = change.getRange(); // guaranteed non-null by Phase 1
            int    startLine = range.getStart().getLine();
            int    startCol  = range.getStart().getCharacter();
            int    endLine   = range.getEnd().getLine();
            int    endCol    = range.getEnd().getCharacter();

            int start = idx.toOffset(startLine, startCol);
            int end   = idx.toOffset(endLine,   endCol);

            int sourceLen = (sb == null) ? current.length() : sb.length();
            if (start < 0 || end < 0 || start > end || end > sourceLen) {
                // Out-of-bounds range — treat the new text as a full replacement
                // and continue applying subsequent changes on top of it.
                current = newText;
                sb  = null;
                idx = new DefinitionFinder.LineIndex(current);
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
                sb.append(current, 0, start);
                sb.append(newText);
                sb.append(current, end, current.length());
                // From here on, the live source is sb, not current.
                idx.rebind(sb);
            } else {
                // Subsequent changes: in-place replace inside the builder.
                sb.replace(start, end, newText);
            }

            // Discard all cached line-start entries from startLine+1 onward:
            // the replacement text may have a different number of newlines.
            // toOffset() will lazily rescan from starts[startLine] as needed.
            idx.applyEdit(startLine);
        }

        return (sb != null) ? sb.toString() : current;
    }

}
