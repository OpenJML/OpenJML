/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.List;
import java.util.function.Function;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextPresentationListener;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.lsp4e.operations.semanticTokens.SemanticTokensClient;
import org.eclipse.lsp4e.operations.semanticTokens.SemanticTokensDataStreamProcessor;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * Applies JML semantic-token coloring inside JDT's Java editor.
 *
 * <p>JDT's Java editor colors {@code //@ …} annotations as plain comments.
 * This class hooks into the viewer's text-presentation pipeline via
 * {@link ITextPresentationListener} and overlays JML keyword / macro / variable
 * colors on top of JDT's own coloring.
 *
 * <p>Colors are resolved by trying LSP4E's {@code TokenTypeMapper} first
 * (same TM4E-theme-based colors as {@code .jml} files) with a hardcoded
 * JFace-registry fallback if reflection fails.
 */
public class JmlColorizer implements ITextPresentationListener {

    private static final String KEY_KEYWORD  = "openjml.jml.keyword";
    private static final String KEY_MACRO    = "openjml.jml.macro";
    private static final String KEY_VARIABLE = "openjml.jml.variable";

    private final ITextViewer viewer;
    private final IDocument   document;

    /** StyleRanges from the most recent server response.  May contain nulls (filtered on apply). */
    private volatile List<StyleRange> cachedRanges = List.of();

    public JmlColorizer(ITextViewer viewer, IDocument document) {
        this.viewer   = viewer;
        this.document = document;
    }

    /**
     * Registers fallback JML colors in JFace's color registry.
     * Must be called from the SWT thread (e.g. inside an asyncExec).
     */
    static void ensureColors() {
        var reg = JFaceResources.getColorRegistry();
        if (!reg.hasValueFor(KEY_KEYWORD))  reg.put(KEY_KEYWORD,  new RGB(155,   0, 155));
        if (!reg.hasValueFor(KEY_MACRO))    reg.put(KEY_MACRO,    new RGB( 63, 127,  95));
        if (!reg.hasValueFor(KEY_VARIABLE)) reg.put(KEY_VARIABLE, new RGB(  0,   0, 192));
    }

    /**
     * Asynchronously requests semantic tokens and updates the presentation.
     * Safe to call from any thread.
     */
    public void refreshAsync() {
        ITextViewer v = viewer;
        SemanticTokensClient.DEFAULT
            .requestFullSemanticTokens(document, (legend, tokens) -> {
                if (tokens == null || tokens.getData() == null) return List.<StyleRange>of();
                var proc = new SemanticTokensDataStreamProcessor(
                        buildTokenMapper(v),
                        pos -> {
                            try {
                                return document.getLineOffset(pos.getLine()) + pos.getCharacter();
                            } catch (BadLocationException e) {
                                return -1;
                            }
                        });
                return proc.getTokensData(tokens.getData(), legend);
            })
            .thenAccept(opt -> {
                cachedRanges = opt.orElse(List.of());
                Display.getDefault().asyncExec(viewer::invalidateTextPresentation);
            });
    }

    /**
     * Builds the token-type mapper.  Tries LSP4E's {@code TokenTypeMapper} via
     * reflection (gives TM4E-theme-consistent colors matching {@code .jml} files).
     * Falls back to a JFace color-registry mapper if reflection fails.
     */
    @SuppressWarnings("unchecked")
    private static Function<String, IToken> buildTokenMapper(ITextViewer viewer) {
        ClassLoader loader = org.openjml.ui.Activator.lsp4eLoader;
        if (loader != null) {
            try {
                Class<?> cls = loader.loadClass(
                        "org.eclipse.lsp4e.operations.semanticTokens.TokenTypeMapper");
                java.lang.reflect.Method create = cls.getMethod("create", ITextViewer.class);
                return (Function<String, IToken>) create.invoke(null, viewer);
            } catch (Exception e) {
                System.err.println("[OpenJML] JmlColorizer: TokenTypeMapper unavailable: " + e);
            }
        }
        // Fallback: use JFace color registry colors pre-registered in ensureColors().
        // ColorRegistry.get() is safe on background threads once colors have been
        // created on the SWT thread.
        var reg = JFaceResources.getColorRegistry();
        return typeName -> {
            String key = switch (typeName) {
                case "keyword"  -> KEY_KEYWORD;
                case "macro"    -> KEY_MACRO;
                case "variable" -> KEY_VARIABLE;
                default -> null;
            };
            if (key == null) return Token.UNDEFINED;
            var color = reg.get(key);
            return color != null ? new Token(new TextAttribute(color)) : Token.UNDEFINED;
        };
    }

    @Override
    public void applyTextPresentation(TextPresentation presentation) {
        List<StyleRange> ranges = cachedRanges;
        if (ranges.isEmpty()) return;
        IRegion extent = presentation.getExtent();
        if (extent == null) return;
        int extStart = extent.getOffset();
        int extEnd   = extStart + extent.getLength();
        for (StyleRange sr : ranges) {
            if (sr == null || sr.foreground == null) continue;
            if (sr.start + sr.length <= extStart || sr.start >= extEnd) continue;
            int clampStart = Math.max(sr.start, extStart);
            int clampEnd   = Math.min(sr.start + sr.length, extEnd);
            if (clampEnd <= clampStart) continue;
            StyleRange clipped = (StyleRange) sr.clone();
            clipped.start  = clampStart;
            clipped.length = clampEnd - clampStart;
            presentation.replaceStyleRange(clipped);
        }
    }
}
