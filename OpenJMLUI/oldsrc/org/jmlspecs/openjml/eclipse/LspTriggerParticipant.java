/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.filebuffers.IDocumentSetupParticipant;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Display;

/**
 * Triggers LSP4E to start the OpenJML language server whenever a Java or JML
 * document is set up, regardless of which editor opens the file.
 *
 * <p>LSP4E's automatic server startup only fires for the Generic Editor. The
 * JDT Java Editor does not trigger it. Registering this participant for
 * {@code org.eclipse.jdt.core.javaSource} and
 * {@code org.jmlspecs.openjml.jmlSource} via
 * {@code org.eclipse.core.filebuffers.documentSetup} ensures LSP4E is
 * notified for every Java/JML file opened, regardless of editor.
 */
public class LspTriggerParticipant implements IDocumentSetupParticipant {

    @Override
    public void setup(IDocument document) {
        System.err.println("[OpenJML] LspTriggerParticipant.setup() called for any doc=" + document.hashCode());
        Display display = Display.getDefault();
        if (display != null) {
            display.asyncExec(() -> triggerLsp(document));
        } else {
            System.err.println("[OpenJML] LspTriggerParticipant: no display");
        }
    }

    private static void triggerLsp(IDocument document) {
        System.err.println("[OpenJML] LspTriggerParticipant.triggerLsp() running");
        try {
            java.util.List<?> servers = org.eclipse.lsp4e.LanguageServiceAccessor.getLanguageServers(
                    document, capabilities -> true);
            System.err.println("[OpenJML] LspTriggerParticipant: getLanguageServers returned " + servers.size() + " server(s)");
        } catch (Exception e) {
            System.err.println("[OpenJML] LspTriggerParticipant: exception: " + e);
        }
    }
}
