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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4e.client.DefaultLanguageClient;
import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.eclipse.lsp4j.PublishDiagnosticsParams;

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

    public OpenJMLLanguageClient() {
        Console.log("[OpenJMLLanguageClient] instantiated");
    }

    /**
     * Creates and schedules a workspace job that deletes all existing
     * {@link OpenJMLConstants#JML_ESC_MARKER} markers on the file and creates
     * new ones for the supplied diagnostics.
     */
    private final Consumer<PublishDiagnosticsParams> escHandler = params -> {
        IResource resource = LSPEclipseUtils.findResourceFor(params.getUri());
        if (!(resource instanceof IFile file) || !file.isAccessible()) return;

        List<Diagnostic> diags = params.getDiagnostics();
        Console.log("[OpenJMLLanguageClient] escHandler uri=" + params.getUri()
                + " markers=" + diags.size());

        var job = new Job("Update ESC markers") {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
                try {
                    IWorkspaceRunnable runnable = m -> updateEscMarkers(file, diags);
                    ResourcesPlugin.getWorkspace().run(runnable,
                            ResourcesPlugin.getWorkspace().getRuleFactory().markerRule(file),
                            0, null);
                } catch (CoreException e) {
                    Console.log("[OpenJMLLanguageClient] ESC marker update failed: " + e.getMessage());
                }
                return Status.OK_STATUS;
            }
        };
        job.setSystem(true);
        job.schedule();
    };

    private static void updateEscMarkers(IFile file, List<Diagnostic> diags)
            throws CoreException {
        // Clear old ESC markers on this file.
        file.deleteMarkers(OpenJMLConstants.JML_ESC_MARKER, false, IResource.DEPTH_ZERO);

        if (diags.isEmpty()) return;

        // Read file content once for char-offset computation.
        int[] lineOffsets = null;
        try (var stream = file.getContents()) {
            String content = new String(stream.readAllBytes(),
                    file.getCharset(false));
            lineOffsets = buildLineOffsets(content);
        } catch (Exception e) {
            // Proceed without char offsets (line-only markers).
        }

        for (Diagnostic d : diags) {
            Map<String, Object> attrs = new HashMap<>();
            attrs.put(IMarker.MESSAGE, d.getMessage());
            attrs.put(IMarker.SEVERITY, toEclipseSeverity(d.getSeverity()));

            var range = d.getRange();
            int startLine = range.getStart().getLine();        // 0-based
            attrs.put(IMarker.LINE_NUMBER, startLine + 1);     // IMarker uses 1-based

            if (lineOffsets != null && startLine < lineOffsets.length) {
                int charStart = lineOffsets[startLine] + range.getStart().getCharacter();
                int endLine   = range.getEnd().getLine();
                int charEnd   = (endLine < lineOffsets.length)
                        ? lineOffsets[endLine] + range.getEnd().getCharacter()
                        : charStart + 1;
                attrs.put(IMarker.CHAR_START, charStart);
                attrs.put(IMarker.CHAR_END,   charEnd);
            }

            IMarker marker = file.createMarker(OpenJMLConstants.JML_ESC_MARKER);
            marker.setAttributes(attrs);
        }
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
     * Builds a table of character offsets for the first character of each line.
     * Index {@code i} is the offset of line {@code i} (0-based).
     */
    private static int[] buildLineOffsets(String content) {
        var offsets = new ArrayList<Integer>();
        offsets.add(0);
        for (int i = 0; i < content.length(); i++) {
            if (content.charAt(i) == '\n') offsets.add(i + 1);
        }
        return offsets.stream().mapToInt(Integer::intValue).toArray();
    }

    /**
     * Wraps the LSP4E-supplied check-diagnostic consumer with a splitter so
     * that ESC diagnostics go to {@link #escHandler} instead.
     */
    @Override
    public void setDiagnosticsConsumer(Consumer<PublishDiagnosticsParams> checkConsumer) {
        Console.log("[OpenJMLLanguageClient] setDiagnosticsConsumer called");
        super.setDiagnosticsConsumer(params -> {
            var checkDiags = new ArrayList<Diagnostic>();
            var escDiags   = new ArrayList<Diagnostic>();
            for (Diagnostic d : params.getDiagnostics()) {
                if (OpenJMLConstants.SOURCE_ESC.equals(d.getSource())) {
                    escDiags.add(d);
                } else {
                    checkDiags.add(d);
                }
            }
            Console.log("[OpenJMLLanguageClient] split uri=" + params.getUri()
                    + " check=" + checkDiags.size() + " esc=" + escDiags.size());
            checkConsumer.accept(new PublishDiagnosticsParams(params.getUri(), checkDiags));
            escHandler.accept(new PublishDiagnosticsParams(params.getUri(), escDiags));
        });
    }
}
