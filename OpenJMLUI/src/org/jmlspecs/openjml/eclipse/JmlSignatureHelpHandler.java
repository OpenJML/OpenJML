/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.net.URI;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.SignatureHelp;
import org.eclipse.lsp4j.SignatureHelpContext;
import org.eclipse.lsp4j.SignatureHelpParams;
import org.eclipse.lsp4j.SignatureHelpTriggerKind;
import org.eclipse.lsp4j.SignatureInformation;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.KeyAdapter;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * Handles the {@code org.jmlspecs.openjml.commands.signatureHelp} command
 * (default key: {@code Ctrl+Shift+J H}).
 *
 * <p>Manually invokes {@code textDocument/signatureHelp} on the OpenJML LSP
 * server and shows the result in a tooltip-style popup near the cursor.
 * This provides parameter-hint display inside JML comment regions, where
 * Eclipse's Java editor does not automatically send {@code signatureHelp}
 * requests (because JML text lives in comment partitions).
 *
 * <p>The popup is dismissed automatically after 6 seconds or when the user
 * presses any key.
 */
public class JmlSignatureHelpHandler extends AbstractHandler {

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        IEditorPart editor = HandlerUtil.getActiveEditor(event);
        if (editor == null) return null;

        var resource = org.eclipse.ui.ide.ResourceUtil.getResource(editor.getEditorInput());
        if (resource == null) return null;
        IDocument doc = LSPEclipseUtils.getDocument(resource);
        if (doc == null) return null;

        ITextSelection sel = (ITextSelection) editor.getSite().getSelectionProvider().getSelection();
        int offset = sel.getOffset();

        Position pos;
        try {
            pos = LSPEclipseUtils.toPosition(offset, doc);
        } catch (BadLocationException e) {
            return null;
        }

        URI docUri = LSPEclipseUtils.toUri(doc);
        if (docUri == null) return null;

        SignatureHelpParams params = new SignatureHelpParams(
                new TextDocumentIdentifier(docUri.toString()),
                pos,
                new SignatureHelpContext(SignatureHelpTriggerKind.Invoked, false));

        LanguageServers.forDocument(doc)
                .computeFirst(ls -> ls.getTextDocumentService().signatureHelp(params))
                .thenAccept(optHelp -> {
                    if (optHelp.isEmpty()) return;
                    SignatureHelp help = optHelp.get();
                    if (help == null || help.getSignatures() == null
                            || help.getSignatures().isEmpty()) return;
                    Display.getDefault().asyncExec(() -> showPopup(editor, help));
                });

        return null;
    }

    // -----------------------------------------------------------------------
    // Popup display
    // -----------------------------------------------------------------------

    private static void showPopup(IEditorPart editor, SignatureHelp help) {
        ITextEditor textEditor = editor.getAdapter(ITextEditor.class);
        if (textEditor == null) return;
        ISourceViewer viewer = textEditor.getAdapter(ISourceViewer.class);
        if (viewer == null) return;
        StyledText st = viewer.getTextWidget();
        if (st == null || st.isDisposed()) return;
        showPopup(st, help);
    }

    /** Package-private entry point used by {@link JmlAutoEditStrategy}. */
    static void showPopup(StyledText st, SignatureHelp help) {
        String text = buildDisplayText(help);

        // Position popup just below the caret line
        int caretOffset = st.getCaretOffset();
        Point caretPt = st.getLocationAtOffset(caretOffset);
        Point screenPt = st.toDisplay(caretPt.x, caretPt.y + st.getLineHeight());

        Shell parentShell = st.getShell();
        Shell popup = new Shell(parentShell, SWT.ON_TOP | SWT.NO_FOCUS | SWT.TOOL);
        popup.setBackground(Display.getDefault().getSystemColor(SWT.COLOR_INFO_BACKGROUND));
        FillLayout layout = new FillLayout();
        layout.marginWidth = 4;
        layout.marginHeight = 2;
        popup.setLayout(layout);

        Label lbl = new Label(popup, SWT.NONE);
        lbl.setBackground(Display.getDefault().getSystemColor(SWT.COLOR_INFO_BACKGROUND));
        lbl.setText(text);

        popup.pack();
        popup.setLocation(screenPt);
        popup.setVisible(true);

        // Dismiss on next keystroke or after 6 seconds
        Display.getDefault().timerExec(6000, () -> {
            if (!popup.isDisposed()) popup.dispose();
        });
        st.addKeyListener(new KeyAdapter() {
            @Override
            public void keyPressed(KeyEvent e) {
                st.removeKeyListener(this);
                if (!popup.isDisposed()) popup.dispose();
            }
        });
    }

    /**
     * Builds the text shown in the popup.
     * Shows the active signature label; if an active parameter is identified,
     * appends an arrow annotation on a second line.
     */
    private static String buildDisplayText(SignatureHelp help) {
        int sigIdx = help.getActiveSignature() != null ? help.getActiveSignature() : 0;
        SignatureInformation sig = help.getSignatures().get(sigIdx);
        String label = sig.getLabel();

        Integer activeParam = help.getActiveParameter();
        if (activeParam == null) activeParam = sig.getActiveParameter();
        if (activeParam != null && sig.getParameters() != null
                && activeParam >= 0 && activeParam < sig.getParameters().size()) {
            var param = sig.getParameters().get(activeParam);
            var paramLabel = param.getLabel();
            String paramName = paramLabel.isLeft()
                    ? paramLabel.getLeft()
                    : label.substring(paramLabel.getRight().getFirst(),
                                      paramLabel.getRight().getSecond());
            return label + "\n  \u2191 " + paramName;
        }
        return label;
    }
}
