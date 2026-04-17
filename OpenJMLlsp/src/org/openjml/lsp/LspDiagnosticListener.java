package org.openjml.lsp;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Collects all diagnostics emitted by OpenJML during a check pass,
 * then converts them to LSP Diagnostic objects on request.
 *
 * <p>Supports per-call <em>capture mode</em> for in-process {@code doESC} runs.
 * When a thread calls {@link #startCapture()}, subsequent {@link #report} calls
 * from that thread go into a thread-local list instead of the shared
 * {@link #collected} list.  {@link #stopCapture()} returns that list and clears it.
 * This lets concurrent {@code doESC} calls on different methods (possibly different
 * threads) each collect only their own diagnostics.
 */
public class LspDiagnosticListener implements DiagnosticListener<JavaFileObject> {

    /** Set to true and recompile to enable per-diagnostic debug logging in toLspDiagnostics(). */
    private static final boolean DEBUG_DIAGNOSTICS = false;

    /**
     * Source tag written into every LSP {@link org.eclipse.lsp4j.Diagnostic} produced
     * by this listener.  Defaults to {@link DiagnosticConverter#SOURCE_CHECK}.
     * Call {@link #setSourceTag} before running the check to override.
     */
    private String sourceTag = DiagnosticConverter.SOURCE_CHECK;

    /**
     * Sets the source tag that will be written into every LSP diagnostic produced
     * by this listener.  Call this once before invoking {@code api.execute()}.
     * Use {@link DiagnosticConverter#SOURCE_CHECK} for {@code --check} runs and
     * {@link DiagnosticConverter#SOURCE_ESC} for {@code --esc} runs.
     */
    public void setSourceTag(String tag) {
        this.sourceTag = tag;
    }

    /**
     * Precomputed line-start offsets for the primary source being checked.
     * Set via {@link #setSourceContent} before {@code api.execute()} so that
     * {@link DiagnosticConverter} can compute accurate tab-safe LSP columns.
     */
    private int[] lineStartOffsets;

    /**
     * Precompute the line-start offset table from the source content.
     * Call this once per check, before {@code api.execute()}, with the exact
     * string that was written to the temp file.
     */
    public void setSourceContent(String content) {
        lineStartOffsets = DiagnosticConverter.buildLineStartOffsets(content);
    }

    private final List<Diagnostic<? extends JavaFileObject>> collected =
            Collections.synchronizedList(new ArrayList<Diagnostic<? extends JavaFileObject>>());

    /** Per-thread capture list; non-null only while a doESC call is active on that thread. */
    private final ThreadLocal<List<Diagnostic<? extends JavaFileObject>>> captureMode =
            new ThreadLocal<>();

    /** Start per-call diagnostic capture on the calling thread. */
    public void startCapture() {
        captureMode.set(new ArrayList<>());
    }

    /**
     * Stop per-call capture and return the diagnostics collected since
     * {@link #startCapture()}.  The thread-local state is cleared.
     */
    public List<Diagnostic<? extends JavaFileObject>> stopCapture() {
        List<Diagnostic<? extends JavaFileObject>> list = captureMode.get();
        captureMode.remove();
        return list != null ? Collections.unmodifiableList(list) : List.of();
    }

    @Override
    public void report(Diagnostic<? extends JavaFileObject> diagnostic) {
        // Investigate: log diagnostics with no source or no position so we can trace
        // tool-level warnings (e.g. bad --warn key) that might otherwise be silently dropped.
        if (diagnostic.getSource() == null || diagnostic.getLineNumber() == Diagnostic.NOPOS) {
            System.err.println("[LspDiagnosticListener.report] nopos/nosource:"
                    + " kind=" + diagnostic.getKind()
                    + " source=" + (diagnostic.getSource() == null ? "<null>"
                                                                    : diagnostic.getSource().getName())
                    + " line=" + diagnostic.getLineNumber()
                    + " code=" + diagnostic.getCode()
                    + " msg=" + diagnostic.getMessage(java.util.Locale.ENGLISH));
        }
        List<Diagnostic<? extends JavaFileObject>> cap = captureMode.get();
        if (cap != null) {
            cap.add(diagnostic);  // capture mode: goes to thread-local list only
        } else {
            collected.add(diagnostic);  // normal mode
        }
    }

    /**
     * Convert a list of raw diagnostics (e.g. from {@link #stopCapture()}) to LSP format.
     *
     * @param rawDiags   diagnostics captured during a {@code doESC} call
     * @param sourcePath temp/real file path used during compilation (for source-filtering)
     * @param targetUri  the LSP document URI to map diagnostics to
     * @param sourceTag  value for {@link org.eclipse.lsp4j.Diagnostic#setSource}; use
     *                   {@link DiagnosticConverter#SOURCE_CHECK} or
     *                   {@link DiagnosticConverter#SOURCE_ESC}
     */
    public static List<org.eclipse.lsp4j.Diagnostic> toLspDiagnosticsFromList(
            List<Diagnostic<? extends JavaFileObject>> rawDiags,
            String sourcePath, String targetUri, String sourceTag) {
        var result = new ArrayList<org.eclipse.lsp4j.Diagnostic>();
        for (var d : rawDiags) {
            if (!DiagnosticConverter.matchesSourcePath(d, sourcePath)) continue;
            result.add(DiagnosticConverter.convert(d, targetUri, null, sourceTag));
        }
        return result;
    }

    public List<Diagnostic<? extends JavaFileObject>> getDiagnostics() {
        return Collections.unmodifiableList(collected);
    }

    /**
     * Returns the plain-text messages of diagnostics that represent tool-level warnings —
     * those with no source file ({@code getSource() == null}) or no source position
     * ({@code getLineNumber() == NOPOS}).  Examples include an unrecognised {@code --warn}
     * key, which OpenJML emits with {@code NOPOS} rather than a real line number.
     * The standard conversion methods skip these; this method surfaces them so callers
     * can route them to the client console via {@code window/logMessage}.
     */
    public List<String> toGlobalMessages() {
        var result = new ArrayList<String>();
        for (var d : collected) {
            // Include null-source diagnostics AND diagnostics with NOPOS that have no
            // meaningful source location — both represent tool-level messages (e.g. a bad
            // --warn key warning) that cannot be attributed to a specific file/line.
            boolean nullSource = (d.getSource() == null);
            boolean noPos = (d.getLineNumber() == Diagnostic.NOPOS);
            if (!nullSource && !noPos) continue;
            String msg = d.getMessage(java.util.Locale.ENGLISH);
            if (msg != null && !msg.isBlank()) result.add(msg);
        }
        return result;
    }

    /**
     * Convert collected diagnostics to LSP Diagnostics.
     *
     * @param sourcePath the temp-file path actually passed to OpenJML (for filtering)
     * @param targetUri  the LSP document URI to report diagnostics against
     */
    /**
     * Return the names of files OTHER than the primary {@code sourcePath} that
     * produced at least one diagnostic (i.e. dependency files whose errors
     * prevented compilation).  Each entry is a plain filename such as
     * {@code "B.java"}, in the order first seen, without duplicates.
     */
    public List<String> toForeignMessages(String sourcePath) {
        String base = baseName(sourcePath);
        List<String> files = new ArrayList<>();
        java.util.Set<String> seen = new java.util.LinkedHashSet<>();
        for (var d : collected) {
            if (d.getSource() == null) continue;
            String srcName = d.getSource().getName();
            if (srcName.isEmpty() || srcName.endsWith(base)) continue;
            String fileName = baseName(srcName);
            if (seen.add(fileName)) files.add(fileName);
        }
        return files;
    }

    private static String baseName(String path) {
        int i = Math.max(path.lastIndexOf('/'), path.lastIndexOf('\\'));
        return path.substring(i + 1);
    }

    /**
     * Convert collected diagnostics for ALL source files, grouped by their
     * {@code file://} URI.  Used for multi-path {@code --dirs} invocations where
     * diagnostics may come from many files.
     *
     * <p>Diagnostics with no source (file-level) are skipped — there is no
     * obvious file to attribute them to in a multi-file context.
     */
    public Map<String, List<org.eclipse.lsp4j.Diagnostic>> toLspDiagnosticsByFile() {
        Map<String, List<org.eclipse.lsp4j.Diagnostic>> result = new LinkedHashMap<>();
        for (var d : collected) {
            if (d.getSource() == null) continue;
            String srcPath = d.getSource().getName();
            if (srcPath.isEmpty()) continue;
            String uri;
            try {
                uri = java.nio.file.Path.of(srcPath).toUri().toString();
            } catch (Exception e) {
                continue;
            }
            result.computeIfAbsent(uri, k -> new ArrayList<>())
                  .add(DiagnosticConverter.convert(d, uri, null, sourceTag));
        }
        return result;
    }

    /**
     * Extract diagnostics for ALL files compiled in this pass.
     *
     * <p>Returns a map from real URI → LSP diagnostic list.  Every URI in
     * {@code tempPathToRealUri} gets an entry (possibly an empty list), so
     * callers can clear markers on files that compiled without errors.
     *
     * @param tempPathToRealUri  maps each temp file path (as returned by
     *                           {@link java.nio.file.Path#toString()}) to its
     *                           real LSP document URI
     */
    public Map<String, List<org.eclipse.lsp4j.Diagnostic>> toLspDiagnosticsAll(
            Map<String, String> tempPathToRealUri) {
        Map<String, List<org.eclipse.lsp4j.Diagnostic>> result = new HashMap<>();
        // Pre-populate with empty lists so files with no errors get their markers cleared.
        for (String realUri : tempPathToRealUri.values()) {
            result.put(realUri, new ArrayList<>());
        }
        for (var d : collected) {
            if (d.getSource() == null) continue;
            for (Map.Entry<String, String> entry : tempPathToRealUri.entrySet()) {
                if (DiagnosticConverter.matchesSourcePath(d, entry.getKey())) {
                    result.get(entry.getValue()).add(DiagnosticConverter.convert(d, entry.getValue(), null, sourceTag));
                    break;
                }
            }
        }
        return result;
    }

    /**
     * Returns the LSP diagnostics currently accumulated for a specific file URI.
     * May be called while {@code api.execute()} is still running to get a
     * mid-run snapshot (e.g. from a {@code ProofResultListener} callback).
     */
    public List<org.eclipse.lsp4j.Diagnostic> getLspDiagnosticsForUri(String uri) {
        var result = new ArrayList<org.eclipse.lsp4j.Diagnostic>();
        for (var d : collected) {
            if (d.getSource() == null) continue;
            String srcPath = d.getSource().getName();
            if (srcPath.isEmpty()) continue;
            String srcUri;
            try { srcUri = java.nio.file.Path.of(srcPath).toUri().toString(); }
            catch (Exception e) { continue; }
            if (uri.equals(srcUri))
                result.add(DiagnosticConverter.convert(d, uri, null, sourceTag));
        }
        return result;
    }

    public List<org.eclipse.lsp4j.Diagnostic> toLspDiagnostics(String sourcePath, String targetUri) {
        var result = new ArrayList<org.eclipse.lsp4j.Diagnostic>();
        for (var d : collected) {
            if (DEBUG_DIAGNOSTICS) {
                String src = d.getSource() == null ? "<null>" : d.getSource().getName();
                System.err.println("  raw: kind=" + d.getKind()
                        + " code=" + d.getCode()
                        + " line=" + d.getLineNumber()
                        + " src=" + src
                        + " msg=" + d.getMessage(java.util.Locale.ENGLISH));
            }
            // Null-source diagnostics are tool-level warnings (e.g. bad --warn key);
            // they are routed to the client console via toGlobalMessages(), not here.
            if (d.getSource() == null) continue;
            if (!DiagnosticConverter.matchesSourcePath(d, sourcePath)) {
                if (DEBUG_DIAGNOSTICS) System.err.println("    ^ filtered (wrong source file)");
                // Log diagnostics that are silently dropped — helps trace tool-level warnings
                // that have a non-null source which doesn't match the target file.
                String dSrc = d.getSource() == null ? "<null>" : d.getSource().getName();
                System.err.println("[LspDiagnosticListener.toLspDiagnostics] filtered:"
                        + " source=" + dSrc
                        + " line=" + d.getLineNumber()
                        + " vs path=" + sourcePath
                        + " msg=" + d.getMessage(java.util.Locale.ENGLISH));
                continue;
            }
            result.add(DiagnosticConverter.convert(d, targetUri, lineStartOffsets, sourceTag));
        }
        return result;
    }
}
