/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;

import java.util.concurrent.CompletableFuture;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4e.client.DefaultLanguageClient;
import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.eclipse.lsp4j.PublishDiagnosticsParams;
import org.eclipse.swt.widgets.Display;

/**
 * Custom LSP4E language client that routes ESC diagnostics to a dedicated
 * {@link OpenJMLConstants#JML_ESC_MARKER} marker type.
 *
 * <p>LSP4E constructs a single {@code LSPDiagnosticsToMarkers} for the marker
 * type declared in {@code plugin.xml} ({@link OpenJMLConstants#JML_PROBLEM_MARKER})
 * and installs it via {@link #setDiagnosticsConsumer}.  This override intercepts
 * that call and wraps the supplied consumer with a splitter that dispatches on
 * {@link Diagnostic#getSource()}:
 *
 * <ul>
 *   <li>Source {@link OpenJMLConstants#SOURCE_ESC} → {@link #escHandler}
 *       (creates {@code JMLESCProblem} markers via Eclipse marker API directly)</li>
 *   <li>Everything else → the original consumer
 *       (creates {@code JMLProblem} markers via LSP4E)</li>
 * </ul>
 *
 * <p>{@link #escHandler} does not use {@code LSPDiagnosticsToMarkers} (which is
 * in an unexported internal package) and instead creates markers directly using
 * the public {@link IResource} API.
 *
 * <p><b>plugin.xml sync</b>: the {@code clientImpl} attribute of the
 * {@code org.eclipse.lsp4e.languageServer} extension must name this class.
 */
public class OpenJMLLanguageClient extends DefaultLanguageClient {

    /**
     * Updates ESC markers immediately on the calling thread.
     *
     * <p>Running synchronously (rather than scheduling a Job) ensures that each
     * per-method {@code publishDiagnostics} notification updates the markers before
     * the next notification arrives, so markers appear incrementally as proofs complete.
     */
    private final Consumer<PublishDiagnosticsParams> escHandler = params -> {
        IResource resource = LSPEclipseUtils.findResourceFor(params.getUri());
        if (!(resource instanceof IFile file) || !file.isAccessible()) return;
        List<Diagnostic> diags = params.getDiagnostics();
        try {
            IWorkspaceRunnable runnable = m -> updateEscMarkers(file, diags);
            ResourcesPlugin.getWorkspace().run(runnable,
                    ResourcesPlugin.getWorkspace().getRuleFactory().markerRule(file),
                    0, null);
        } catch (CoreException e) {
            Console.log("[OpenJMLLanguageClient] ESC marker update failed: " + e.getMessage());
        }
    };

    private static void updateEscMarkers(IFile file, List<Diagnostic> diags)
            throws CoreException {
        // Clear old ESC markers on this file.
        file.deleteMarkers(OpenJMLConstants.JML_ESC_MARKER, false, IResource.DEPTH_ZERO);

        if (diags.isEmpty()) return;

        // Prefer the live IDocument (file open in editor); fall back to reading the file
        // directly and building a line-start offset table for files not open in any editor.
        org.eclipse.jface.text.IDocument doc = LSPEclipseUtils.getDocument(file);
        int[] lineOffsets = null;
        if (doc == null) {
            try (java.io.InputStream in = file.getContents()) {
                String content = new String(in.readAllBytes(),
                        file.getCharset() != null ? java.nio.charset.Charset.forName(file.getCharset())
                                                  : java.nio.charset.StandardCharsets.UTF_8);
                lineOffsets = buildLineOffsets(content);
            } catch (Exception e) {
                // Could not read file — char offsets will be omitted for all diagnostics.
            }
        }

        for (Diagnostic d : diags) {
            Map<String, Object> attrs = new HashMap<>();
            attrs.put(IMarker.MESSAGE, d.getMessage());
            attrs.put(IMarker.SEVERITY, toEclipseSeverity(d.getSeverity()));

            var range = d.getRange();
            int startLine = range.getStart().getLine();        // 0-based
            attrs.put(IMarker.LINE_NUMBER, startLine + 1);     // IMarker uses 1-based

            if (doc != null) {
                try {
                    int charStart = doc.getLineOffset(startLine) + range.getStart().getCharacter();
                    int charEnd   = doc.getLineOffset(range.getEnd().getLine()) + range.getEnd().getCharacter();
                    attrs.put(IMarker.CHAR_START, charStart);
                    attrs.put(IMarker.CHAR_END,   charEnd);
                } catch (org.eclipse.jface.text.BadLocationException e) {
                    // Line out of range — skip char offsets for this diagnostic.
                }
            } else if (lineOffsets != null) {
                int endLine = range.getEnd().getLine();
                if (startLine < lineOffsets.length && endLine < lineOffsets.length) {
                    attrs.put(IMarker.CHAR_START, lineOffsets[startLine] + range.getStart().getCharacter());
                    attrs.put(IMarker.CHAR_END,   lineOffsets[endLine]   + range.getEnd().getCharacter());
                }
            }

            IMarker marker = file.createMarker(OpenJMLConstants.JML_ESC_MARKER);
            marker.setAttributes(attrs);
        }
    }

    /** Returns a 0-based array where {@code result[i]} is the char offset of the start of line {@code i}. */
    private static int[] buildLineOffsets(String content) {
        java.util.List<Integer> offsets = new java.util.ArrayList<>();
        offsets.add(0);
        int pos = 0;
        while ((pos = content.indexOf('\n', pos)) >= 0) {
            offsets.add(++pos);
        }
        return offsets.stream().mapToInt(Integer::intValue).toArray();
    }

    /** Maps LSP {@link DiagnosticSeverity} to {@link IMarker} severity integer. */
    private static int toEclipseSeverity(DiagnosticSeverity sev) {
        if (sev == null) return IMarker.SEVERITY_ERROR;
        return switch (sev) {
            case Error   -> IMarker.SEVERITY_ERROR;
            case Warning -> IMarker.SEVERITY_WARNING;
            default      -> IMarker.SEVERITY_INFO;
        };
    }

    /**
     * Overrides the base implementation, which runs on a ForkJoinPool thread
     * where {@code UI.getActivePage()} returns null and the update is silently
     * skipped.  Dispatches to the SWT UI thread instead and walks all open
     * editors directly.
     */
    @Override
    public CompletableFuture<Void> refreshCodeLenses() {
        Display display = Display.getDefault();
        if (display != null && !display.isDisposed())
            display.asyncExec(LspPartListener::refreshAllCodeMinings);
        return CompletableFuture.completedFuture(null);
    }

    /** Package-private access to the language server for {@link OpenJMLCodeMiningProvider}. */
    org.eclipse.lsp4j.services.LanguageServer server() {
        return getLanguageServer();
    }

    /**
     * The original LSP4E consumer ({@code LSPDiagnosticsToMarkers} for
     * {@link OpenJMLConstants#JML_PROBLEM_MARKER}), captured on the first call.
     * Used to route check diagnostics (including empty → clear stale markers)
     * without going through the LspPartListener hook chain on re-entry.
     */
    private Consumer<PublishDiagnosticsParams> lsp4eConsumer;

    /**
     * The outermost consumer as seen by our splitting wrapper.  Initially the
     * same as {@link #lsp4eConsumer}; updated to the LspPartListener hook
     * wrapper when that hook calls {@link #setDiagnosticsConsumer} again.
     * Must be volatile because it is written on the UI/hook thread and read on
     * LSP notification delivery threads.
     */
    private volatile Consumer<PublishDiagnosticsParams> hookConsumer;

    /**
     * Guards against re-entrant invocation of our splitting wrapper.
     *
     * <p>LspPartListener installs a hook by reading the {@code diagnosticConsumer}
     * field from {@code DefaultLanguageClient} and wrapping it:
     * {@code hookWrapper = p -> { ourWrapper(p); refreshColorizer(); }}.
     * It then calls {@link #setDiagnosticsConsumer(Consumer) setDiagnosticsConsumer(hookWrapper)},
     * which (via our override) updates {@link #hookConsumer} to {@code hookWrapper}
     * without installing a second wrapper.
     *
     * <p>When a notification arrives, the delivery sequence on one thread is:
     * <ol>
     *   <li>{@code ourWrapper(params)} — inSplitter=false → set true, split diags</li>
     *   <li>{@code hookConsumer(checkList)} = {@code hookWrapper(checkList)}</li>
     *   <li>{@code hookWrapper} calls {@code ourWrapper(checkList)} (re-entrant)</li>
     *   <li>inSplitter=true → call {@code lsp4eConsumer(checkList)} directly and return</li>
     *   <li>{@code hookWrapper} calls {@code refreshColorizer()}</li>
     *   <li>Back in step 1: {@code escHandler(escList)}</li>
     * </ol>
     * This ensures {@code lsp4eConsumer} always receives the check list (even when empty,
     * which clears stale check markers) while {@code escHandler} always receives the ESC list.
     */
    private final ThreadLocal<Boolean> inSplitter = ThreadLocal.withInitial(() -> false);

    /**
     * Wraps the LSP4E-supplied check-diagnostic consumer with a splitter so
     * that ESC diagnostics go to {@link #escHandler} instead.
     * Also registers this client with {@link OpenJMLCodeMiningProvider}.
     *
     * <p>The splitting wrapper is installed only once (on the first call from the
     * LSP4E framework).  Subsequent calls — notably from LspPartListener's
     * {@code installDiagnosticsHook}, which wraps the already-installed wrapper
     * and calls this method again — only update {@link #hookConsumer} so that
     * check-diag notifications flow through the hook (enabling its colorizer refresh)
     * without triggering a second wrapper and the double-ESC-wipe bug.
     */
    @Override
    public void setDiagnosticsConsumer(Consumer<PublishDiagnosticsParams> consumer) {
        OpenJMLCodeMiningProvider.languageClient = this;
        if (lsp4eConsumer == null) {
            // First call from LSP4E: install the splitting wrapper once.
            lsp4eConsumer = consumer;
            hookConsumer  = consumer;
            super.setDiagnosticsConsumer(params -> {
                if (inSplitter.get()) {
                    // Re-entrant: we are inside hookConsumer which called back into
                    // our wrapper (LspPartListener hook chain).  Route directly to
                    // lsp4eConsumer to avoid infinite recursion.
                    lsp4eConsumer.accept(params);
                    return;
                }
                inSplitter.set(true);
                try {
                    var checkList = new ArrayList<Diagnostic>();
                    var escList   = new ArrayList<Diagnostic>();
                    for (Diagnostic d : params.getDiagnostics()) {
                        if (OpenJMLConstants.SOURCE_ESC.equals(d.getSource())) escList.add(d);
                        else checkList.add(d);
                    }
                    Console.log("[OpenJMLLanguageClient] publishDiagnostics uri=" + params.getUri()
                            + " check=" + checkList.size() + " esc=" + escList.size());
                    // Route check diags through hookConsumer (may include LspPartListener's
                    // colorizer refresh).  On re-entry the guard routes to lsp4eConsumer.
                    // An empty checkList clears stale check markers — always forward it.
                    hookConsumer.accept(new PublishDiagnosticsParams(params.getUri(), checkList));
                    // ESC diags go directly to our marker handler, bypassing LSP4E.
                    // An empty escList clears stale ESC markers — always forward it.
                    escHandler.accept(new PublishDiagnosticsParams(params.getUri(), escList));
                } finally {
                    inSplitter.set(false);
                }
            });
        } else {
            // Subsequent call (e.g. LspPartListener wrapping our wrapper):
            // update hookConsumer so future check notifications flow through the new hook.
            // Do NOT install another wrapper — the one above is already in place.
            hookConsumer = consumer;
        }
    }
}
