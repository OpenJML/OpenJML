/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.Map;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.text.IDocument;
import org.eclipse.lsp4e.operations.diagnostics.IMarkerAttributeComputer;
import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;

/**
 * LSP4E marker-attribute computer that routes OpenJML LSP diagnostics to
 * the correct custom Eclipse marker type and normalizes the severity attribute.
 *
 * <p>The LSP server stamps {@link OpenJMLConstants#SOURCE_ESC} on every
 * {@code --esc} diagnostic and {@link OpenJMLConstants#SOURCE_CHECK} on every
 * {@code --check} diagnostic.  This class reads that tag and:
 * <ul>
 *   <li>For ESC diagnostics — overrides the marker type to
 *       {@link OpenJMLConstants#JML_ESC_MARKER} and forces
 *       {@code IMarker.SEVERITY_ERROR}.  Verification failures are emitted by
 *       the javac back-end as {@code Kind.WARNING}, so the LSP severity arrives
 *       as {@code Warning}; the override makes them appear as errors in Eclipse.</li>
 *   <li>For check diagnostics — leaves the marker type as
 *       {@link OpenJMLConstants#JML_PROBLEM_MARKER} (the default configured
 *       via the {@code markerType} attribute on the {@code languageServer}
 *       element in {@code plugin.xml}) and normalises {@code IMarker.SEVERITY}
 *       from the LSP severity.</li>
 * </ul>
 *
 * <p>Registered via the {@code markerAttributeComputer} attribute on the
 * {@code languageServer} element in {@code plugin.xml}.
 *
 * <p><b>plugin.xml sync</b>: the class name here must match the
 * {@code markerAttributeComputer} attribute value in the
 * {@code org.eclipse.lsp4e.languageServer} extension.
 */
public class OpenJMLMarkerAttributeComputer implements IMarkerAttributeComputer {

    @Override
    public void addMarkerAttributesForDiagnostic(
            Diagnostic diagnostic,
            IDocument document,
            IResource resource,
            Map<String, Object> attributes) {

        String src = diagnostic.getSource();

        if (OpenJMLConstants.SOURCE_ESC.equals(src)) {
            // Route ESC diagnostics to the JMLESCProblem marker type.
            attributes.put(IMarker.MARKER_TYPE, OpenJMLConstants.JML_ESC_MARKER);
            // Verification failures are reported by the javac back-end as
            // Kind.WARNING (not Kind.ERROR), so the LSP severity arrives as
            // Warning.  Override to ERROR so they appear as errors in Eclipse.
            attributes.put(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
        } else {
            // For check diagnostics: normalise IMarker.SEVERITY to the Integer
            // form so the annotation framework can match on markerSeverity.
            // Check diagnostics stay with the default JMLProblem marker type.
            DiagnosticSeverity sev = diagnostic.getSeverity();
            if (sev != null) {
                int markerSeverity = switch (sev) {
                    case Error       -> IMarker.SEVERITY_ERROR;
                    case Warning     -> IMarker.SEVERITY_WARNING;
                    case Information,
                         Hint        -> IMarker.SEVERITY_INFO;
                };
                attributes.put(IMarker.SEVERITY, markerSeverity);
            }
        }
    }
}
