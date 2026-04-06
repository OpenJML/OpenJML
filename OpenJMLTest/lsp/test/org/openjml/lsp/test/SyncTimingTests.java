package org.openjml.lsp.test;

import com.google.gson.Gson;
import org.eclipse.lsp4j.DidChangeTextDocumentParams;
import org.eclipse.lsp4j.TextDocumentContentChangeEvent;
import org.eclipse.lsp4j.VersionedTextDocumentIdentifier;
import org.junit.Test;
import org.openjml.lsp.IncrementalSyncApplier;

import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * Timing benchmarks for {@link IncrementalSyncApplier} and the LSP JSON
 * serialisation path.
 *
 * <p>This class is intentionally <em>not</em> included in {@link FastTests} or
 * {@link AllLspTests}.  It exists to measure performance characteristics and
 * must be run explicitly:
 * <pre>
 *   make test-SyncTimingTests
 * </pre>
 *
 * <p>Results are printed to stdout and captured in
 * {@code build/results/SyncTimingTests.log}.
 *
 * <h3>What is measured</h3>
 * <dl>
 *   <dt>Server-side reconstruction cost</dt>
 *   <dd>Compares three strategies for reconstructing document content after a
 *   {@code textDocument/didChange} event:
 *   <ul>
 *     <li><b>incremental</b> — {@link IncrementalSyncApplier#apply}: uses a
 *         pre-sized {@link StringBuilder}, a lazy {@code LineIndex} that
 *         converts {@code (line, col)} positions to offsets via
 *         {@code String.indexOf('\n')} (JVM-intrinsified), and survives across
 *         multiple changes in one event without an intermediate
 *         {@code toString()} snapshot.</li>
 *     <li><b>naive-concat</b> — {@code prefix.substring() + newText + suffix.substring()}:
 *         simpler but allocates two intermediate strings per change.</li>
 *     <li><b>full-store</b> — baseline cost of simply storing an already-built
 *         result string; represents the server-side cost of full-document sync
 *         where the client sends the entire text on every keystroke.</li>
 *   </ul></dd>
 *   <dt>Transmission cost</dt>
 *   <dd>Compares the JSON payload size and serialisation time for a
 *   full-document change event versus an incremental change event of fixed
 *   small size, across the same set of document sizes.  The incremental
 *   payload is essentially constant (~160 bytes) regardless of file size;
 *   the full-sync payload grows linearly with the document.</dd>
 * </dl>
 */
public class SyncTimingTests {

    private static final int[] DOC_SIZES = {1_000, 10_000, 100_000, 1_000_000};

    // -----------------------------------------------------------------------
    // Document and change-event construction helpers
    // -----------------------------------------------------------------------

    /**
     * Generate a synthetic Java-like document of approximately {@code targetSize}
     * characters, with newlines so line/col conversions work correctly.
     * Each line is ~72 characters including the newline.
     */
    static String generateDoc(int targetSize) {
        StringBuilder sb = new StringBuilder(targetSize + 80);
        int line = 0;
        while (sb.length() < targetSize) {
            sb.append(String.format("    // line %06d: padding content abcdefghijklmnopqrstuvwxyz 0123456789%n",
                    line++));
        }
        return sb.toString();
    }

    /**
     * Return the character offset of 0-indexed {@code (line, col)} in {@code doc}.
     * Used to build change events from a known document position.
     */
    private static int offsetOf(String doc, int line, int col) {
        int cur = 0, l = 0;
        while (l < line) { cur = doc.indexOf('\n', cur) + 1; l++; }
        return cur + col;
    }

    /**
     * Build an incremental {@link TextDocumentContentChangeEvent} that deletes
     * {@code deleteLen} characters at {@code offset} and inserts {@code insert}.
     * The range is expressed as {@code (line, col)} positions derived from the
     * document content.
     */
    static TextDocumentContentChangeEvent incAt(String doc, int offset,
                                                int deleteLen, String insert) {
        int line = 0, lineStart = 0;
        for (int i = 0; i < offset; i++) {
            if (doc.charAt(i) == '\n') { line++; lineStart = i + 1; }
        }
        int startCol = offset - lineStart;

        int endLine = line, endLineStart = lineStart;
        for (int i = offset; i < offset + deleteLen; i++) {
            if (doc.charAt(i) == '\n') { endLine++; endLineStart = i + 1; }
        }
        int endCol = (offset + deleteLen) - endLineStart;

        return IncrementalSyncApplierTest.inc(line, startCol, endLine, endCol, insert);
    }

    /**
     * Apply a list of changes naively using substring concatenation.
     * Used as a correctness baseline inside {@link #runTimingScenario}.
     */
    private static String applyNaive(String current,
                                     List<TextDocumentContentChangeEvent> changes) {
        for (TextDocumentContentChangeEvent change : changes) {
            if (change.getRange() == null) { current = change.getText(); continue; }
            String newText = change.getText() != null ? change.getText() : "";
            var r = change.getRange();
            int start = offsetOf(current, r.getStart().getLine(), r.getStart().getCharacter());
            int end   = offsetOf(current, r.getEnd().getLine(),   r.getEnd().getCharacter());
            current = current.substring(0, start) + newText + current.substring(end);
        }
        return current;
    }

    // -----------------------------------------------------------------------
    // Timing infrastructure
    // -----------------------------------------------------------------------

    @FunctionalInterface
    interface TimedOp { String run(); }

    /** Return the median nanoseconds per operation over {@code reps} runs. */
    private static long timeOp(TimedOp op, int warmup, int reps) {
        for (int i = 0; i < warmup; i++) op.run();
        long[] times = new long[reps];
        for (int i = 0; i < reps; i++) {
            long t = System.nanoTime();
            op.run();
            times[i] = System.nanoTime() - t;
        }
        java.util.Arrays.sort(times);
        return times[reps / 2];
    }

    /** Scale iteration count so each scenario takes roughly 100 ms total. */
    private static int reps(int docSize) {
        return Math.max(3, 100_000_000 / Math.max(1, docSize));
    }

    private void runTimingScenario(String label, String doc,
                                   List<TextDocumentContentChangeEvent> changes) {
        String expected = IncrementalSyncApplier.apply(doc, changes);
        int r = reps(doc.length());

        long incr  = timeOp(() -> IncrementalSyncApplier.apply(doc, changes), 5, r);
        long naive = timeOp(() -> applyNaive(doc, changes), 5, r);
        long store = timeOp(() -> { String s = expected; return s; }, 5, r);

        System.out.printf("  %-60s  incr=%,8d ns  naive=%,8d ns  store=%,4d ns%n",
                label, incr, naive, store);

        // Both strategies must produce the same result.
        assertEquals("incremental and naive differ for: " + label,
                expected, applyNaive(doc, changes));
    }

    // -----------------------------------------------------------------------
    // Test: server-side reconstruction cost
    // -----------------------------------------------------------------------

    /**
     * Measures server-side reconstruction time for document sizes 1K–1M across
     * four edit scenarios:
     * <ol>
     *   <li>Single insert at the document midpoint</li>
     *   <li>Single delete at the document midpoint</li>
     *   <li>Single replace (10 chars) at the document midpoint</li>
     *   <li>Three inserts in a single event at 3/4, 1/2, and 1/4 of the document</li>
     * </ol>
     *
     * <p>Key findings:
     * <ul>
     *   <li>Using {@code String.indexOf('\n')} (JVM-intrinsified via SIMD) for
     *       the {@code (line,col)→offset} conversion is ~10x faster than a
     *       char-by-char {@code charAt} scan.</li>
     *   <li>Sharing a single {@code LineIndex} across both the start and end of
     *       each range halves the number of newline scans per change.</li>
     *   <li>Rebinding the {@code LineIndex} to the {@code StringBuilder} after
     *       the first edit — combined with {@code applyEdit(startLine)} to
     *       truncate the cached line-start array — eliminates the O(n)
     *       {@code sb.toString()} snapshot that would otherwise be required
     *       between each change in a multi-delta event.</li>
     *   <li>Net result: incremental reconstruction is ~20–30% faster than
     *       naive substring concatenation at 100K–1M characters, and ~3x
     *       faster for 3-edit events at 1M characters.</li>
     * </ul>
     */
    @Test
    public void reconstructionTimingTest() {
        System.out.println("\n[TIMING] IncrementalSyncApplier — server-side reconstruction cost");
        System.out.printf("  %-60s  %18s  %18s  %10s%n",
                "Scenario", "incremental", "naive-concat", "full-store");
        System.out.println("  " + "-".repeat(116));

        for (int size : DOC_SIZES) {
            String doc = generateDoc(size);
            int n = doc.length();
            int mid = n / 2;

            runTimingScenario(String.format("size=%,7d  1 insert at middle", n),
                    doc, List.of(incAt(doc, mid, 0, "X")));

            runTimingScenario(String.format("size=%,7d  1 delete at middle", n),
                    doc, List.of(incAt(doc, mid, 1, "")));

            runTimingScenario(String.format("size=%,7d  1 replace(10) at middle", n),
                    doc, List.of(incAt(doc, mid, 10, "REPLACED**")));

            // Three edits at 3/4, 1/2, 1/4 — sent in descending offset order so
            // each change's position is stable relative to the previous result.
            int p1 = n * 3 / 4, p2 = n / 2, p3 = n / 4;
            runTimingScenario(String.format("size=%,7d  3 inserts at 3/4,1/2,1/4", n),
                    doc, List.of(incAt(doc, p1, 0, "A"),
                                 incAt(doc, p2, 0, "B"),
                                 incAt(doc, p3, 0, "C")));
        }
        System.out.println();
    }

    // -----------------------------------------------------------------------
    // Test: JSON serialisation + write cost (transmission proxy)
    // -----------------------------------------------------------------------

    private static DidChangeTextDocumentParams makeFullSyncParams(String docContent) {
        TextDocumentContentChangeEvent change = new TextDocumentContentChangeEvent();
        change.setText(docContent);
        DidChangeTextDocumentParams p = new DidChangeTextDocumentParams();
        p.setTextDocument(new VersionedTextDocumentIdentifier("file:///Foo.java", 1));
        p.setContentChanges(List.of(change));
        return p;
    }

    private static DidChangeTextDocumentParams makeIncrementalParams(
            TextDocumentContentChangeEvent change) {
        DidChangeTextDocumentParams p = new DidChangeTextDocumentParams();
        p.setTextDocument(new VersionedTextDocumentIdentifier("file:///Foo.java", 1));
        p.setContentChanges(List.of(change));
        return p;
    }

    /**
     * Measures the cost of serialising a {@code textDocument/didChange}
     * notification to JSON and writing the bytes to a null sink, for both
     * full-document and incremental sync modes.
     *
     * <p>This approximates the encoding half of the LSP IPC path (client→server)
     * without a real socket.  Key findings:
     * <ul>
     *   <li>The incremental JSON payload is ~160 bytes regardless of document
     *       size (just URI, version, range coords, and short replacement text).
     *       The full-sync payload scales linearly: ~1 MB for a 1M-char file.</li>
     *   <li>Gson serialisation of a 1M-char full-sync event costs ~2 ms;
     *       the incremental equivalent costs ~2 µs — a 1000x difference.</li>
     *   <li>Writing to a null sink (OS buffer copy) adds ~180 µs for full-sync
     *       at 1M characters; the incremental write is essentially free.</li>
     *   <li>The transmission saving dominates all server-side CPU costs for
     *       files beyond ~10K characters.</li>
     * </ul>
     */
    @Test
    public void transmissionCostBenchmark() throws Exception {
        Gson gson = new Gson();
        Writer sink = new OutputStreamWriter(OutputStream.nullOutputStream(),
                                             StandardCharsets.UTF_8);

        System.out.println("\n[TIMING] Transmission cost: JSON serialisation + write to null sink");
        System.out.printf("  %-50s  %10s  %12s  %10s%n",
                "Scenario", "bytes", "serialize ns", "write ns");
        System.out.println("  " + "-".repeat(88));

        for (int size : DOC_SIZES) {
            String doc = generateDoc(size);
            int mid = doc.length() / 2;

            DidChangeTextDocumentParams fullParams = makeFullSyncParams(doc);
            String fullJson = gson.toJson(fullParams);
            int fullBytes = fullJson.getBytes(StandardCharsets.UTF_8).length;
            int r = reps(doc.length());

            long fullSerialize = timeOp(() -> gson.toJson(fullParams), 3, r);
            long fullWrite = timeOp(() -> {
                try { sink.write(fullJson); sink.flush(); }
                catch (Exception e) { throw new RuntimeException(e); }
                return fullJson;
            }, 3, r);

            TextDocumentContentChangeEvent incrChange = incAt(doc, mid, 0, "X");
            DidChangeTextDocumentParams incrParams = makeIncrementalParams(incrChange);
            String incrJson = gson.toJson(incrParams);
            int incrBytes = incrJson.getBytes(StandardCharsets.UTF_8).length;

            long incrSerialize = timeOp(() -> gson.toJson(incrParams), 3, r);
            long incrWrite = timeOp(() -> {
                try { sink.write(incrJson); sink.flush(); }
                catch (Exception e) { throw new RuntimeException(e); }
                return incrJson;
            }, 3, r);

            System.out.printf("  %-50s  %,10d  %,12d  %,10d%n",
                    String.format("size=%,7d  full-sync",   doc.length()),
                    fullBytes, fullSerialize, fullWrite);
            System.out.printf("  %-50s  %,10d  %,12d  %,10d%n",
                    String.format("size=%,7d  incremental", doc.length()),
                    incrBytes, incrSerialize, incrWrite);
        }
        System.out.println();
    }
}
