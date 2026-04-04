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
 * LSP4E marker-attribute computer that routes OpenJML LSP diagnostics to
 * the correct custom Eclipse marker type and normalizes the severity attribute.
 *
 * <p>The LSP server stamps {@link OpenJMLConstants#SOURCE_ESC} on every
 * {@code --esc} diagnostic and {@link OpenJMLConstants#SOURCE_CHECK} on every
 * {@code --check} diagnostic.  This class reads that tag and:
 * <ul>
 *   <li>For ESC diagnostics — overrides the marker type to
 *       {@link OpenJMLConstants#JML_ESC_MARKER} and maps severity as follows:
 *       {@code Error} or {@code Warning} → {@code SEVERITY_ERROR} (verification
 *       failures; javac emits them as {@code Kind.WARNING});
 *       {@code Information} or {@code Hint} → {@code SEVERITY_INFO} (associated-
 *       declaration messages that accompany a proof failure).</li>
 *   <li>For check diagnostics — leaves the marker type as
 *       {@link OpenJMLConstants#JML_PROBLEM_MARKER} (the default configured
 *       via the {@code markerType} attribute on the {@code languageServer}
 *       element in {@code plugin.xml}) and maps {@code Error} → {@code SEVERITY_ERROR},
 *       {@code Warning} → {@code SEVERITY_WARNING}, anything else → {@code SEVERITY_INFO}.</li>
 * </ul>
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
            Diagnostic diagnostic, // LSP diagnostic
            IDocument document,
            IResource resource,
            Map<String, Object> attributes) {

        String src = diagnostic.getSource();
        String code = diagnostic.getCode().getLeft();
        Console.log("DIAGNOSTIC CODE " + code + " " + diagnostic.getSeverity());

        //if (OpenJMLConstants.SOURCE_ESC.equals(src)) {
        if ("compiler.warn.esc.assertion.invalid".equals(code)) {
            // Route ESC diagnostics to the JMLESCProblem marker type.
            attributes.put(IMarker.MARKER, OpenJMLConstants.JML_ESC_MARKER);
            // Verification failures arrive as Warning (javac Kind.WARNING).
            // Associated-declaration info messages arrive as Information/Hint.
            DiagnosticSeverity sev = diagnostic.getSeverity();
            int markerSeverity = (sev == DiagnosticSeverity.Warning
                                  || sev == DiagnosticSeverity.Error)
                    ? IMarker.SEVERITY_ERROR   // verification failure
                    : IMarker.SEVERITY_INFO;   // associated info
            attributes.put(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
        } else if (code.startsWith("compiler.warn.jml.associated.decl")) {
            // Route ESC diagnostics to the JMLESCProblem marker type.
            attributes.put(IMarker.MARKER, OpenJMLConstants.JML_ESC_MARKER);
            attributes.put(IMarker.SEVERITY, IMarker.SEVERITY_INFO);
        } else {
            // Check diagnostics: map severity directly.
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
