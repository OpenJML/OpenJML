/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextPresentationListener;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.lsp4j.services.LanguageServer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * Applies JML semantic-token coloring inside JDT's Java editor.
 *
 * <p>JDT's Java editor colors {@code //@ …} annotations as plain comments.
 * This class hooks into the viewer's text-presentation pipeline via
 * {@link ITextPresentationListener} and overlays JML semantic-token colors
 * on top of JDT's own coloring.
 *
 * <p>Tokens are fetched by sending {@code openjml.getSemanticTokens} via
 * {@code workspace/executeCommand} directly to the OpenJML server (using the
 * cached {@code LanguageServerWrapper} from {@link LspPartListener}).  This
 * bypasses LSP4E's normal semantic-token routing, which routes
 * {@code textDocument/semanticTokens/full} to JDT for {@code .java} files.
 *
 * <p>Colors and styles (bold/italic/underline/strikethrough) are read from the
 * OpenJML preference store ({@link OpenJMLOptions#TOKEN_COLORS}).  The JFace
 * color registry is used as a cache; it is refreshed on every
 * {@link #refreshAsync()} call via {@link #ensureColors()}.  LSP4E's
 * {@code TokenTypeMapper} is tried first for {@code .jml} files (TM4E theme
 * colors); the preference-store fallback is used when TM4E returns no color.
 */
public class JmlColorizer implements ITextPresentationListener {

    /**
     * Maps a token-type id (from the server legend) to its index in
     * {@link OpenJMLOptions#TOKEN_COLORS}.  Built once on first use.
     */
    private static final java.util.Map<String, OpenJMLOptions.TokenColorEntry> TOKEN_COLOR_MAP;
    static {
        var map = new java.util.HashMap<String, OpenJMLOptions.TokenColorEntry>();
        for (OpenJMLOptions.TokenColorEntry e : OpenJMLOptions.TOKEN_COLORS) map.put(e.id(), e);
        TOKEN_COLOR_MAP = java.util.Collections.unmodifiableMap(map);
    }

    /**
     * Token type names in legend index order — must match
     * {@code SemanticTokensProvider.TOKEN_TYPES} exactly.
     */
    private static final String[] TOKEN_TYPE_NAMES = {
        "namespace", "class", "interface", "enum", "struct",
        "typeParameter", "type", "parameter", "variable", "property",
        "enumMember", "method", "function", "macro", "keyword",
        "modifier", "decorator", "comment", "string", "number", "operator"
    };

    private final ITextViewer viewer;
    private final IDocument   document;
    private final String      fileUri;

    /** StyleRanges from the most recent server response.  May contain nulls (filtered on apply). */
    private volatile List<StyleRange> cachedRanges = List.of();

    public JmlColorizer(ITextViewer viewer, IDocument document, String fileUri) {
        this.viewer   = viewer;
        this.document = document;
        this.fileUri  = fileUri;
    }

    /**
     * Registers JML token colors in JFace's color registry from the preference store.
     * Must be called from the SWT thread (e.g. inside an asyncExec).
     * Safe to call repeatedly — existing entries are overwritten so that preference
     * changes take effect without restarting Eclipse.
     */
    static void ensureColors() {
        IPreferenceStore store;
        try {
            store = org.openjml.ui.Activator.getDefault().getPreferenceStore();
        } catch (Exception e) {
            // Activator not running (plugin not yet started or already stopped).
            // Console is also unavailable, so write directly to the Eclipse error log.
            org.eclipse.core.runtime.Platform.getLog(JmlColorizer.class).log(
                    new org.eclipse.core.runtime.Status(
                            org.eclipse.core.runtime.IStatus.ERROR, JmlColorizer.class,
                            "JmlColorizer.ensureColors: could not load JML token colors"
                            + " — OpenJML Activator not running", e));
            return;
        }
        var reg = JFaceResources.getColorRegistry();
        for (OpenJMLOptions.TokenColorEntry entry : OpenJMLOptions.TOKEN_COLORS) {
            RGB rgb = PreferenceConverter.getColor(store, entry.colorKey());
            reg.put(entry.colorKey(), rgb);
        }
    }

    /**
     * Returns a {@link TextAttribute} for the given token type id, reading colors
     * and styles from the preference store.  Returns {@code null} for unknown types.
     *
     * <p>Must be called from the SWT thread so that {@link Color} objects are
     * created on the correct display.
     */
    private static TextAttribute textAttributeFor(String typeId) {
        OpenJMLOptions.TokenColorEntry entry = TOKEN_COLOR_MAP.get(typeId);
        if (entry == null) return null;
        Color color = JFaceResources.getColorRegistry().get(entry.colorKey());
        if (color == null) return null;
        IPreferenceStore store;
        try {
            store = org.openjml.ui.Activator.getDefault().getPreferenceStore();
        } catch (Exception e) {
            return null;
        }
        int style = OpenJMLOptions.getTokenStyle(store, entry);
        return new TextAttribute(color, null, style);
    }

    /**
     * Asynchronously requests semantic tokens from the OpenJML server and
     * updates the text presentation.  Safe to call from any thread.
     *
     * <p>Sends {@code openjml.getSemanticTokens} via {@code workspace/executeCommand}
     * using the cached {@link LspPartListener#cachedWrapper}.  This bypasses
     * LSP4E's routing (which would direct {@code textDocument/semanticTokens/full}
     * to JDT for {@code .java} files).
     */
    public void refreshAsync() {
        Object wrapper = LspPartListener.cachedWrapper;
        if (wrapper == null) return;
        ITextViewer v = viewer;
        Function<String, IToken> mapper = buildTokenMapper(v);
        var params = new ExecuteCommandParams(
                OpenJMLConstants.CMD_GET_SEMANTIC_TOKENS, List.of(fileUri));
        executeViaWrapper(wrapper, params)
            .thenAccept(raw -> {
                if (raw == null) return;
                // Decoding reads JFace color registry (SWT-owned) and creates StyleRanges,
                // so do it on the SWT thread together with ensureColors() and the invalidation.
                Display.getDefault().asyncExec(() -> {
                    ensureColors();
                    List<StyleRange> ranges = decodeTokenData(raw, mapper);
                    cachedRanges = ranges;
                    viewer.invalidateTextPresentation();
                });
            })
            .exceptionally(t -> {
                Console.errorlog("JmlColorizer.refreshAsync failed", t);
                return null;
            });
    }

    /**
     * Sends {@code params} to the OpenJML server via the cached
     * {@code LanguageServerWrapper} and returns the result future.
     * Returns an immediately-completed future with {@code null} on any error.
     */
    private static java.util.concurrent.CompletableFuture<Object> executeViaWrapper(
            Object wrapper, ExecuteCommandParams params) {
        try {
            java.lang.reflect.Method getServer = null;
            for (Class<?> c = wrapper.getClass(); c != null && c != Object.class;
                    c = c.getSuperclass()) {
                try {
                    getServer = c.getDeclaredMethod("getServer");
                    getServer.setAccessible(true);
                    break;
                } catch (NoSuchMethodException ignored) {}
            }
            if (getServer == null) {
                return java.util.concurrent.CompletableFuture.completedFuture(null);
            }
            Object sf = getServer.invoke(wrapper);
            LanguageServer server = null;
            if (sf instanceof java.util.concurrent.CompletableFuture<?> cf)
                server = (LanguageServer) cf.get(5, java.util.concurrent.TimeUnit.SECONDS);
            else if (sf instanceof LanguageServer ls)
                server = ls;
            if (server == null) {
                return java.util.concurrent.CompletableFuture.completedFuture(null);
            }
            @SuppressWarnings("unchecked")
            var fut = (java.util.concurrent.CompletableFuture<Object>)
                      server.getWorkspaceService().executeCommand(params);
            return fut;
        } catch (Exception e) {
            Console.errorlog("JmlColorizer.executeViaWrapper failed", e);
            return java.util.concurrent.CompletableFuture.completedFuture(null);
        }
    }

    /**
     * Decodes the raw token data returned by {@code openjml.getSemanticTokens}
     * into a list of {@link StyleRange} objects.
     *
     * <p>The server returns a flat {@code List<Integer>} of delta-encoded 5-tuples
     * {@code [deltaLine, deltaStartChar, length, tokenTypeIndex, tokenModifiers]}.
     * Gson deserializes JSON numbers as {@code Double} when the declared type is
     * {@code Object}, so each element is cast via {@link Number#intValue()}.
     *
     * <p>Colors and styles (bold/italic/underline/strikethrough) are read from the
     * preference store via {@link #textAttributeFor(String)}.
     */
    // Built-in modifier bit masks — must match SemanticTokensProvider.TM_* constants.
    private static final int TM_DECLARATION =  1;  // bit 0 → bold
    private static final int TM_STATIC      =  8;  // bit 3 → italic
    private static final int TM_DEPRECATED  = 16;  // bit 4 → strikethrough
    private static final int TM_ABSTRACT    = 32;  // bit 5 → italic

    private List<StyleRange> decodeTokenData(Object raw, Function<String, IToken> mapper) {
        if (!(raw instanceof List<?> list)) return List.of();
        List<StyleRange> result = new ArrayList<>();
        int line = 0, col = 0;
        for (int i = 0; i + 4 < list.size(); i += 5) {
            int dLine   = toInt(list.get(i));
            int dCol    = toInt(list.get(i + 1));
            int len     = toInt(list.get(i + 2));
            int typeIdx = toInt(list.get(i + 3));
            int modMask = toInt(list.get(i + 4));
            line += dLine;
            col   = (dLine == 0) ? col + dCol : dCol;
            if (typeIdx < 0 || typeIdx >= TOKEN_TYPE_NAMES.length) continue;
            String typeName = TOKEN_TYPE_NAMES[typeIdx];

            // Try preference-store colors first (own TextAttribute with color+style).
            TextAttribute ta = textAttributeFor(typeName);
            // Fall back to the TM4E/JFace mapper when the preference store has no entry.
            if (ta == null || ta.getForeground() == null) {
                IToken token = mapper.apply(typeName);
                if (token == null || token == Token.UNDEFINED) continue;
                if (!(token.getData() instanceof TextAttribute)) continue;
                ta = (TextAttribute) token.getData();
            }
            if (ta == null || ta.getForeground() == null) continue;

            try {
                int offset = document.getLineOffset(line) + col;
                StyleRange sr = new StyleRange(offset, len, ta.getForeground(), null);
                int style = ta.getStyle();
                sr.fontStyle = style & (SWT.BOLD | SWT.ITALIC);
                sr.underline = (style & TextAttribute.UNDERLINE) != 0;
                sr.strikeout = (style & TextAttribute.STRIKETHROUGH) != 0;

                // Built-in modifier styles (applied on top of preference-store styles).
                if ((modMask & TM_DECLARATION) != 0)             sr.fontStyle |= SWT.BOLD;
                if ((modMask & (TM_STATIC | TM_ABSTRACT)) != 0) sr.fontStyle |= SWT.ITALIC;
                if ((modMask & TM_DEPRECATED) != 0)              sr.strikeout  = true;

                result.add(sr);
            } catch (BadLocationException ignored) {}
        }
        return result;
    }

    private static int toInt(Object o) {
        return (o instanceof Number n) ? n.intValue() : 0;
    }

    /**
     * Builds the token-type mapper used as a fallback when
     * {@link #textAttributeFor(String)} returns null (unknown type or color
     * registry not yet populated).
     *
     * <p>Tries LSP4E's {@code TokenTypeMapper} via reflection first (gives
     * TM4E-theme-consistent colors for {@code .jml} files).  Falls back to the
     * JFace color-registry (populated by {@link #ensureColors()}).
     */
    @SuppressWarnings("unchecked")
    private static Function<String, IToken> buildTokenMapper(ITextViewer viewer) {
        // Build the JFace-registry fallback (uses per-type preference-store keys).
        var reg = JFaceResources.getColorRegistry();
        Function<String, IToken> fallback = typeName -> {
            OpenJMLOptions.TokenColorEntry entry = TOKEN_COLOR_MAP.get(typeName);
            if (entry == null) return Token.UNDEFINED;
            var color = reg.get(entry.colorKey());
            if (color == null) return Token.UNDEFINED;
            IPreferenceStore store;
            try {
                store = org.openjml.ui.Activator.getDefault().getPreferenceStore();
            } catch (Exception ex) {
                return new Token(new TextAttribute(color));
            }
            int style = OpenJMLOptions.getTokenStyle(store, entry);
            return new Token(new TextAttribute(color, null, style));
        };

        // Try TM4E-based TokenTypeMapper.  For .java files in Eclipse there is no TM4E grammar,
        // so TokenTypeMapper returns tokens with null foreground for every type name.  Chain it
        // with the JFace fallback: use TM4E's color only when its foreground is non-null.
        ClassLoader loader = org.openjml.ui.Activator.lsp4eLoader;
        if (loader != null) {
            try {
                Class<?> cls = loader.loadClass(
                        "org.eclipse.lsp4e.operations.semanticTokens.TokenTypeMapper");
                java.lang.reflect.Method create = cls.getMethod("create", ITextViewer.class);
                create.setAccessible(true);
                Function<String, IToken> tm4e = (Function<String, IToken>) create.invoke(null, viewer);
                return typeName -> {
                    IToken t = tm4e.apply(typeName);
                    if (t != null && t != Token.UNDEFINED
                            && t.getData() instanceof TextAttribute ta
                            && ta.getForeground() != null) {
                        return t;
                    }
                    return fallback.apply(typeName);
                };
            } catch (Exception e) {
                Console.errorlog("JmlColorizer: TokenTypeMapper unavailable", e);
            }
        }
        return fallback;
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
