/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.net.URI;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.CompletionItem;
import org.eclipse.lsp4j.CompletionParams;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.SignatureHelp;
import org.eclipse.lsp4j.SignatureHelpContext;
import org.eclipse.lsp4j.SignatureHelpParams;
import org.eclipse.lsp4j.SignatureHelpTriggerKind;
import org.eclipse.lsp4j.SignatureInformation;
import org.eclipse.lsp4j.TextDocumentIdentifier;

/**
 * Supplies JML keyword completions and parameter hints inside JML comment
 * regions ({@code //@} and {@code /*@}) in Java source files opened by the
 * JDT editor.
 *
 * <p>LSP4E's automatic content-assist and signature-help triggers are
 * suppressed in comment partitions by the JDT Java editor.  This class
 * restores that functionality for JML annotations specifically:
 * <ul>
 *   <li>{@link #computeCompletionProposals} — JML keyword / backslash-token
 *       completions, delegated to the OpenJML LSP server via
 *       {@code textDocument/completion}.</li>
 *   <li>{@link #computeContextInformation} — parameter hints for method
 *       calls inside JML expressions, delegated to the OpenJML LSP server
 *       via {@code textDocument/signatureHelp}.</li>
 * </ul>
 *
 * <p>Both methods return an empty result when the cursor is not inside a
 * JML annotation, so they are harmless when triggered in plain Java comments.
 *
 * <p>Registered in {@code plugin.xml} for partition types
 * {@code __java_singleline_comment} and {@code __java_multiline_comment}.
 */
public class ProposalComputer implements IJavaCompletionProposalComputer {

    private static final int LSP_TIMEOUT_MS = 2000;

    @Override public void sessionStarted() {}
    @Override public void sessionEnded()   {}
    @Override public String getErrorMessage() { return null; }

    // -----------------------------------------------------------------------
    // Keyword / backslash-token completions
    // -----------------------------------------------------------------------

    @Override
    public List<ICompletionProposal> computeCompletionProposals(
            ContentAssistInvocationContext context, IProgressMonitor monitor) {
        IDocument doc  = context.getDocument();
        int       offset = context.getInvocationOffset();

        Position pos = toLspPosition(doc, offset);
        if (pos == null) return List.of();

        URI docUri = LSPEclipseUtils.toUri(doc);
        if (docUri == null) return List.of();

        CompletionParams params = new CompletionParams(
                new TextDocumentIdentifier(docUri.toString()), pos);

        try {
            var opt = LanguageServers.forDocument(doc)
                    .computeFirst(ls -> ls.getTextDocumentService().completion(params))
                    .get(LSP_TIMEOUT_MS, TimeUnit.MILLISECONDS);
            if (opt.isEmpty() || opt.get() == null) return List.of();

            List<CompletionItem> items = opt.get().isLeft()
                    ? opt.get().getLeft()
                    : opt.get().getRight().getItems();
            if (items == null || items.isEmpty()) return List.of();

            List<ICompletionProposal> result = new ArrayList<>(items.size());
            for (CompletionItem item : items) {
                ICompletionProposal p = toJdtProposal(item, doc, offset, pos);
                if (p != null) result.add(p);
            }
            return result;
        } catch (Exception e) {
            return List.of();
        }
    }

    // -----------------------------------------------------------------------
    // Parameter hints (context information)
    // -----------------------------------------------------------------------

    @Override
    public List<IContextInformation> computeContextInformation(
            ContentAssistInvocationContext context, IProgressMonitor monitor) {
        IDocument doc    = context.getDocument();
        int       offset = context.getInvocationOffset();

        Position pos = toLspPosition(doc, offset);
        if (pos == null) return List.of();

        URI docUri = LSPEclipseUtils.toUri(doc);
        if (docUri == null) return List.of();

        SignatureHelpParams params = new SignatureHelpParams(
                new TextDocumentIdentifier(docUri.toString()),
                pos,
                new SignatureHelpContext(SignatureHelpTriggerKind.Invoked, false));

        try {
            var opt = LanguageServers.forDocument(doc)
                    .computeFirst(ls -> ls.getTextDocumentService().signatureHelp(params))
                    .get(LSP_TIMEOUT_MS, TimeUnit.MILLISECONDS);
            if (opt.isEmpty() || opt.get() == null) return List.of();

            SignatureHelp help = opt.get();
            if (help.getSignatures() == null || help.getSignatures().isEmpty()) return List.of();

            List<IContextInformation> result = new ArrayList<>();
            for (SignatureInformation sig : help.getSignatures()) {
                result.add(new SignatureContextInfo(sig.getLabel()));
            }
            return result;
        } catch (Exception e) {
            return List.of();
        }
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static Position toLspPosition(IDocument doc, int offset) {
        try {
            return LSPEclipseUtils.toPosition(offset, doc);
        } catch (BadLocationException e) {
            return null;
        }
    }

    private static ICompletionProposal toJdtProposal(CompletionItem item, IDocument doc,
                                                      int offset, Position pos) {
        String label = item.getLabel();
        String insertText = item.getInsertText() != null ? item.getInsertText() : label;

        // If the server supplied an explicit text edit, honour its range.
        if (item.getTextEdit() != null && item.getTextEdit().isLeft()) {
            var edit = item.getTextEdit().getLeft();
            try {
                int start = LSPEclipseUtils.toOffset(edit.getRange().getStart(), doc);
                int end   = LSPEclipseUtils.toOffset(edit.getRange().getEnd(),   doc);
                return new CompletionProposal(edit.getNewText(), start, end - start,
                        start + edit.getNewText().length(), null, label, null, null);
            } catch (BadLocationException ignored) {}
        }

        // Fallback: replace the word currently being typed.
        int wordStart = offset;
        try {
            while (wordStart > 0) {
                char c = doc.getChar(wordStart - 1);
                if (c == '\\' || Character.isLetterOrDigit(c) || c == '_') wordStart--;
                else break;
            }
        } catch (BadLocationException ignored) {}

        return new CompletionProposal(insertText, wordStart, offset - wordStart,
                wordStart + insertText.length(), null, label, null, null);
    }

    // -----------------------------------------------------------------------
    // IContextInformation implementation for signature hints
    // -----------------------------------------------------------------------

    private static class SignatureContextInfo implements IContextInformation {
        private final String text;
        SignatureContextInfo(String text) { this.text = text; }

        @Override public String getContextDisplayString()     { return text; }
        @Override public String getInformationDisplayString() { return text; }
        @Override public org.eclipse.swt.graphics.Image getImage() { return null; }
    }
}
