/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.Map;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.text.IDocument;
import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;

/**
 * LSP4E marker-attribute computer for JML type-check ({@code --check})
 * diagnostics.  Maps LSP {@link DiagnosticSeverity} to Eclipse
 * {@link IMarker#SEVERITY} for {@link OpenJMLConstants#JML_PROBLEM_MARKER}
 * markers.
 *
 * <p>ESC diagnostics ({@link OpenJMLConstants#SOURCE_ESC}) are handled
 * separately by {@link OpenJMLLanguageClient}, which routes them to a
 * dedicated {@link OpenJMLConstants#JML_ESC_MARKER} handler.  This class
 * only sees check diagnostics.
 *
 * <p>Registered via the {@code markerAttributeComputer} attribute on the
 * {@code languageServer} element in {@code plugin.xml}.
 *
 * <p><b>plugin.xml sync</b>: the class name here must match the
 * {@code markerAttributeComputer} attribute value in the
 * {@code org.eclipse.lsp4e.languageServer} extension.
 */
public class OpenJMLMarkerAttributeComputer implements org.eclipse.lsp4e.IMarkerAttributeComputer {

    @Override
    public void addMarkerAttributesForDiagnostic(
            Diagnostic diagnostic,
            IDocument document,
            IResource resource,
            Map<String, Object> attributes) {

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
