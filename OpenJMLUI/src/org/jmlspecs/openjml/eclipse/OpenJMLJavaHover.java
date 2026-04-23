/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import org.eclipse.jdt.ui.text.java.hover.IJavaEditorTextHover;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4j.Hover;
import org.eclipse.lsp4j.HoverParams;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.eclipse.lsp4j.services.LanguageServer;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;

/**
 * Hover provider for OpenJML in the JDT Java editor.
 *
 * <p>LSP4E's built-in {@code LSPTextHover} is registered via
 * {@code org.eclipse.ui.genericeditor.hoverProviders}, which only fires for
 * the generic text editor — not for the JDT Java editor.  This class implements
 * {@link IJavaEditorTextHover} so that it is invoked by JDT's hover framework
 * for {@code .java} files, including positions inside JML comments
 * ({@code //@ ...}).
 *
 * <p>The hover content (JML spec lines above the method under the cursor) is
 * retrieved synchronously from the OpenJML LSP server with a short timeout.
 */
public class OpenJMLJavaHover implements IJavaEditorTextHover {

    private static final int HOVER_TIMEOUT_MS = 1500;

    private IEditorPart editor;

    @Override
    public void setEditor(IEditorPart editor) {
        this.editor = editor;
    }

    @Override
    public IRegion getHoverRegion(ITextViewer textViewer, int offset) {
        return new Region(offset, 0);
    }

    @Override
    public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
        OpenJMLLanguageClient lc = OpenJMLCodeMiningProvider.languageClient;
        if (lc == null) return null;

        LanguageServer ls = lc.server();
        if (ls == null) return null;

        String uri = getFileUri();
        if (uri == null) return null;

        var doc = textViewer.getDocument();
        if (doc == null) return null;

        int offset = hoverRegion.getOffset();
        try {
            int line = doc.getLineOfOffset(offset);
            int col  = offset - doc.getLineOffset(line);
            HoverParams params = new HoverParams(
                    new TextDocumentIdentifier(uri),
                    new Position(line, col));

            CompletableFuture<Hover> future =
                    ls.getTextDocumentService().hover(params);
            Hover hover = future.get(HOVER_TIMEOUT_MS, TimeUnit.MILLISECONDS);
            if (hover == null || hover.getContents() == null) return null;

            return extractText(hover);
        } catch (TimeoutException e) {
            return null;
        } catch (Exception e) {
            return null;
        }
    }

    private String getFileUri() {
        IEditorPart ep = editor;
        // Fall back to the active editor if setEditor was not called yet.
        if (ep == null) {
            var page = org.eclipse.ui.PlatformUI.getWorkbench()
                    .getActiveWorkbenchWindow() != null
                    ? org.eclipse.ui.PlatformUI.getWorkbench()
                            .getActiveWorkbenchWindow().getActivePage()
                    : null;
            ep = (page != null) ? page.getActiveEditor() : null;
        }
        if (ep == null) return null;
        if (ep.getEditorInput() instanceof IFileEditorInput fei) {
            var uri = LSPEclipseUtils.toUri(fei.getFile());
            return uri != null ? uri.toString() : null;
        }
        return null;
    }

    /** Extract a plain-text string from the hover contents. */
    private static String extractText(Hover hover) {
        var contents = hover.getContents();
        if (contents.isLeft()) {
            // MarkedString or List<MarkedString>
            var list = contents.getLeft();
            if (list.isEmpty()) return null;
            var sb = new StringBuilder();
            for (var ms : list) {
                String val = ms.isLeft() ? ms.getLeft() : ms.getRight().getValue();
                if (val != null && !val.isBlank()) {
                    if (sb.length() > 0) sb.append('\n');
                    sb.append(val);
                }
            }
            return sb.isEmpty() ? null : sb.toString();
        } else {
            // MarkupContent
            var mc = contents.getRight();
            return (mc != null && mc.getValue() != null && !mc.getValue().isBlank())
                    ? mc.getValue() : null;
        }
    }
}
