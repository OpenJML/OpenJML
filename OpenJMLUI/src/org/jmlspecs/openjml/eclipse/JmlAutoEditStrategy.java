/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.net.URI;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentCommand;
import org.eclipse.jface.text.IAutoEditStrategy;
import org.eclipse.jface.text.IDocument;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.SignatureHelp;
import org.eclipse.lsp4j.SignatureHelpContext;
import org.eclipse.lsp4j.SignatureHelpParams;
import org.eclipse.lsp4j.SignatureHelpTriggerKind;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.widgets.Display;

/**
 * Intercepts {@code (} and {@code ,} keystrokes in JML comment regions of Java source
 * files and triggers an OpenJML signature-help popup.
 *
 * <p>Eclipse's JDT Java editor suppresses LSP4E's automatic
 * {@code textDocument/signatureHelp} trigger inside comment partitions
 * ({@code __java_singleline_comment}, {@code __java_multiline_comment}).
 * This strategy is attached to the Java editor for those partitions when a
 * {@code .java} editor is opened, restoring automatic signature-help for JML
 * annotations such as {@code //@ assert m(} or {@code /*@ requires foo(bar,}.
 *
 * <p>Installed by {@link LspPartListener} via reflective
 * {@code prependAutoEditStrategy} calls (to avoid OSGi cross-bundle
 * {@code instanceof} issues with {@code AdaptedSourceViewer}).
 */
class JmlAutoEditStrategy implements IAutoEditStrategy {

    private static final Pattern SINGLE_LINE_JML = Pattern.compile("//\\s*@");
    private static final Pattern BLOCK_JML_OPEN  = Pattern.compile("/\\*\\s*@");

    /** The editor's StyledText widget, used to position the popup. */
    private final StyledText styledText;

    JmlAutoEditStrategy(StyledText styledText) {
        this.styledText = styledText;
    }

    @Override
    public void customizeDocumentCommand(IDocument document, DocumentCommand command) {
        // React to ( or , — also handle "()" which JDT's bracket-inserter generates for (
        boolean isOpen  = "(".equals(command.text) || "()".equals(command.text);
        boolean isComma = ",".equals(command.text);
        if (!isOpen && !isComma) return;
        if (!isInJmlRegion(document, command.offset)) return;

        // After the document command is applied the cursor will be after the (.
        // For "()" the cursor ends up at offset+1 (between the parens).
        // We schedule the LSP call via asyncExec so the document has already
        // been updated when we query it.
        int queryOffset   = command.offset + 1;   // always just after the (
        String triggerChar = isComma ? "," : "(";

        Display.getDefault().asyncExec(() -> {
            StyledText st = styledText;
            if (st == null || st.isDisposed()) return;

            URI docUri = LSPEclipseUtils.toUri(document);
            if (docUri == null) return;

            Position pos;
            try {
                pos = LSPEclipseUtils.toPosition(queryOffset, document);
            } catch (BadLocationException e) {
                return;
            }

            SignatureHelpContext ctx = new SignatureHelpContext(
                    SignatureHelpTriggerKind.TriggerCharacter, false);
            ctx.setTriggerCharacter(triggerChar);
            SignatureHelpParams params = new SignatureHelpParams(
                    new TextDocumentIdentifier(docUri.toString()), pos, ctx);

            System.err.println("[AutoEdit] signatureHelp request: uri=" + docUri + " pos=" + pos);
            LanguageServers.forDocument(document)
                    .computeFirst(ls -> ls.getTextDocumentService().signatureHelp(params))
                    .thenAccept(optHelp -> {
                        System.err.println("[AutoEdit] signatureHelp response: present=" + optHelp.isPresent()
                                + (optHelp.isPresent() && optHelp.get() != null
                                        ? " sigs=" + optHelp.get().getSignatures() : ""));
                        if (optHelp.isEmpty()) return;
                        SignatureHelp help = optHelp.get();
                        if (help == null || help.getSignatures() == null
                                || help.getSignatures().isEmpty()) return;
                        Display.getDefault().asyncExec(
                                () -> JmlSignatureHelpHandler.showPopup(st, help));
                    });
        });
    }

    // -----------------------------------------------------------------------
    // JML region detection
    // -----------------------------------------------------------------------

    /**
     * Returns {@code true} when {@code offset} is inside a JML annotation.
     * Recognises single-line ({@code //@}) and block ({@code /*@}) JML comments.
     */
    private static boolean isInJmlRegion(IDocument document, int offset) {
        try {
            // Single-line: check whether //@ appears before the offset on this line
            int line      = document.getLineOfOffset(offset);
            int lineStart = document.getLineOffset(line);
            String linePrefix = document.get(lineStart, offset - lineStart);
            if (SINGLE_LINE_JML.matcher(linePrefix).find()) return true;

            // Block comment: find the last /*@ opener before offset and check it's unclosed
            String before = document.get(0, offset);
            Matcher opener = BLOCK_JML_OPEN.matcher(before);
            int lastOpen = -1;
            while (opener.find()) lastOpen = opener.start();
            if (lastOpen < 0) return false;
            return before.indexOf("*/", lastOpen + 2) < 0;
        } catch (BadLocationException e) {
            return false;
        }
    }
}
