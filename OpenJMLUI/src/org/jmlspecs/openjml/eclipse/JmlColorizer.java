/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

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
import org.eclipse.swt.custom.StyleRange;
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
 * <p>Colors are resolved by trying LSP4E's {@code TokenTypeMapper} first
 * (same TM4E-theme-based colors as {@code .jml} files) with a hardcoded
 * JFace-registry fallback if reflection fails.
 */
public class JmlColorizer implements ITextPresentationListener {

    // Fallback color keys (used when TM4E TokenTypeMapper is unavailable via reflection).
    // Token type names match the 21-entry legend in SemanticTokensProvider.LEGEND.
    private static final String KEY_KEYWORD   = "openjml.jml.keyword";   // "keyword", "modifier"
    private static final String KEY_FUNCTION  = "openjml.jml.function";  // "function" (backslash tokens)
    private static final String KEY_TYPE      = "openjml.jml.type";      // "class","interface","enum","struct","typeParameter","type","enumMember","namespace"
    private static final String KEY_METHOD    = "openjml.jml.method";    // "method"
    private static final String KEY_VARIABLE  = "openjml.jml.variable";  // "variable","parameter","property"
    private static final String KEY_DECORATOR = "openjml.jml.decorator"; // "decorator"
    private static final String KEY_LITERAL   = "openjml.jml.literal";   // "string","number"
    private static final String KEY_OPERATOR  = "openjml.jml.operator";  // "operator"

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
     * Registers fallback JML colors in JFace's color registry.
     * Must be called from the SWT thread (e.g. inside an asyncExec).
     */
    static void ensureColors() {
        var reg = JFaceResources.getColorRegistry();
        if (!reg.hasValueFor(KEY_KEYWORD))   reg.put(KEY_KEYWORD,   new RGB(155,   0, 155)); // purple
        if (!reg.hasValueFor(KEY_FUNCTION))  reg.put(KEY_FUNCTION,  new RGB( 63, 127,  95)); // muted green
        if (!reg.hasValueFor(KEY_TYPE))      reg.put(KEY_TYPE,      new RGB(  0, 128, 128)); // teal
        if (!reg.hasValueFor(KEY_METHOD))    reg.put(KEY_METHOD,    new RGB(  0, 100,  50)); // dark teal
        if (!reg.hasValueFor(KEY_VARIABLE))  reg.put(KEY_VARIABLE,  new RGB(  0,   0, 192)); // blue
        if (!reg.hasValueFor(KEY_DECORATOR)) reg.put(KEY_DECORATOR, new RGB(128, 100,   0)); // dark gold
        if (!reg.hasValueFor(KEY_LITERAL))   reg.put(KEY_LITERAL,   new RGB(  0,   0, 220)); // bright blue
        if (!reg.hasValueFor(KEY_OPERATOR))  reg.put(KEY_OPERATOR,  new RGB( 80,  80,  80)); // dark grey
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
        System.err.println("[JmlColorizer] refreshAsync uri=" + fileUri
                + " wrapper=" + (wrapper != null ? wrapper.getClass().getSimpleName() : "null"));
        if (wrapper == null) return;
        ITextViewer v = viewer;
        Function<String, IToken> mapper = buildTokenMapper(v);
        var params = new ExecuteCommandParams(
                OpenJMLConstants.CMD_GET_SEMANTIC_TOKENS, List.of(fileUri));
        executeViaWrapper(wrapper, params)
            .thenAccept(raw -> {
                System.err.println("[JmlColorizer] raw result type="
                        + (raw != null ? raw.getClass().getName() : "null")
                        + " value=" + (raw instanceof List<?> l ? "List[" + l.size() + "]" : raw));
                if (raw == null) return;
                List<StyleRange> ranges = decodeTokenData(raw, mapper);
                System.err.println("[JmlColorizer] decoded " + ranges.size() + " StyleRanges");
                cachedRanges = ranges;
                Display.getDefault().asyncExec(viewer::invalidateTextPresentation);
            })
            .exceptionally(t -> {
                System.err.println("[JmlColorizer] executeCommand failed: " + t);
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
                System.err.println("[JmlColorizer] executeViaWrapper: getServer method not found on "
                        + wrapper.getClass().getName());
                return java.util.concurrent.CompletableFuture.completedFuture(null);
            }
            Object sf = getServer.invoke(wrapper);
            System.err.println("[JmlColorizer] getServer() returned: "
                    + (sf != null ? sf.getClass().getName() : "null"));
            LanguageServer server = null;
            if (sf instanceof java.util.concurrent.CompletableFuture<?> cf)
                server = (LanguageServer) cf.get(5, java.util.concurrent.TimeUnit.SECONDS);
            else if (sf instanceof LanguageServer ls)
                server = ls;
            if (server == null) {
                System.err.println("[JmlColorizer] executeViaWrapper: could not obtain LanguageServer");
                return java.util.concurrent.CompletableFuture.completedFuture(null);
            }
            System.err.println("[JmlColorizer] sending " + params.getCommand() + " to "
                    + server.getClass().getName());
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
     */
    private List<StyleRange> decodeTokenData(Object raw, Function<String, IToken> mapper) {
        if (!(raw instanceof List<?> list)) return List.of();
        List<StyleRange> result = new ArrayList<>();
        int line = 0, col = 0;
        for (int i = 0; i + 4 < list.size(); i += 5) {
            int dLine   = toInt(list.get(i));
            int dCol    = toInt(list.get(i + 1));
            int len     = toInt(list.get(i + 2));
            int typeIdx = toInt(list.get(i + 3));
            line += dLine;
            col   = (dLine == 0) ? col + dCol : dCol;
            if (typeIdx < 0 || typeIdx >= TOKEN_TYPE_NAMES.length) continue;
            String typeName = TOKEN_TYPE_NAMES[typeIdx];
            IToken token = mapper.apply(typeName);
            if (token == null || token == Token.UNDEFINED) continue;
            if (!(token.getData() instanceof TextAttribute ta)) continue;
            if (ta.getForeground() == null) continue;
            try {
                int offset = document.getLineOffset(line) + col;
                result.add(new StyleRange(offset, len, ta.getForeground(), null));
            } catch (BadLocationException ignored) {}
        }
        return result;
    }

    private static int toInt(Object o) {
        return (o instanceof Number n) ? n.intValue() : 0;
    }

    /**
     * Builds the token-type mapper.  Tries LSP4E's {@code TokenTypeMapper} via
     * reflection (gives TM4E-theme-consistent colors matching {@code .jml} files).
     * Falls back to a JFace color-registry mapper if reflection fails.
     */
    @SuppressWarnings("unchecked")
    private static Function<String, IToken> buildTokenMapper(ITextViewer viewer) {
        // Build the JFace-registry fallback first (always available).
        var reg = JFaceResources.getColorRegistry();
        Function<String, IToken> fallback = typeName -> {
            // Map all 21 legend token types to fallback color keys.
            // Types "macro" (13) and "comment" (17) are declared in the legend but never emitted.
            String key = switch (typeName) {
                case "keyword", "modifier"                                             -> KEY_KEYWORD;
                case "function"                                                        -> KEY_FUNCTION;
                case "namespace", "class", "interface", "enum",
                     "struct", "typeParameter", "type", "enumMember"                  -> KEY_TYPE;
                case "method"                                                          -> KEY_METHOD;
                case "variable", "parameter", "property"                              -> KEY_VARIABLE;
                case "decorator"                                                       -> KEY_DECORATOR;
                case "string", "number"                                                -> KEY_LITERAL;
                case "operator"                                                        -> KEY_OPERATOR;
                default                                                                -> null;
            };
            if (key == null) return Token.UNDEFINED;
            var color = reg.get(key);
            return color != null ? new Token(new TextAttribute(color)) : Token.UNDEFINED;
        };

        // Try TM4E-based TokenTypeMapper.  For .java files in Eclipse there is no TM4E grammar,
        // so TokenTypeMapper returns tokens with null foreground for every type name.  Chain it
        // with the JFace fallback: use TM4E's color only when its foreground is non-null.
        ClassLoader loader = org.openjml.ui.Activator.lsp4eLoader;
        System.err.println("[JmlColorizer] buildTokenMapper: lsp4eLoader=" + loader);
        if (loader != null) {
            try {
                Class<?> cls = loader.loadClass(
                        "org.eclipse.lsp4e.operations.semanticTokens.TokenTypeMapper");
                java.lang.reflect.Method create = cls.getMethod("create", ITextViewer.class);
                create.setAccessible(true);
                Function<String, IToken> tm4e = (Function<String, IToken>) create.invoke(null, viewer);
                System.err.println("[JmlColorizer] buildTokenMapper: chaining TokenTypeMapper + JFace fallback");
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
                System.err.println("[JmlColorizer] buildTokenMapper: TokenTypeMapper failed: " + e);
                Console.errorlog("JmlColorizer: TokenTypeMapper unavailable", e);
            }
        }
        System.err.println("[JmlColorizer] buildTokenMapper: using JFace fallback only");
        return fallback;
    }

    @Override
    public void applyTextPresentation(TextPresentation presentation) {
        List<StyleRange> ranges = cachedRanges;
        if (ranges.isEmpty()) {
            System.err.println("[JmlColorizer] applyTextPresentation: no cached ranges");
            return;
        }
        System.err.println("[JmlColorizer] applyTextPresentation: applying " + ranges.size() + " ranges");
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
