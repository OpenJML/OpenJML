package org.openjml.lsp;

import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import org.eclipse.lsp4j.InlayHint;
import org.eclipse.lsp4j.InlayHintKind;
import org.eclipse.lsp4j.InlayHintParams;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.util.ArrayList;
import java.util.List;

/**
 * Provides {@code textDocument/inlayHints} showing the inferred type of
 * {@code var}-declared local variables.
 *
 * <p>For each {@link JCVariableDecl} in the attributed AST where
 * {@link JCVariableDecl#declaredUsingVar()} is {@code true}, an
 * {@link InlayHint} of kind {@link InlayHintKind#Type} is emitted immediately
 * after the variable name in the form {@code : TypeName}.
 *
 * <p>The type string is shortened by stripping:
 * <ul>
 *   <li>{@code java.lang.} — always removed (e.g. {@code String} not
 *       {@code java.lang.String})</li>
 *   <li>The containing file's own package prefix — removes noise for types
 *       declared in the same package.</li>
 * </ul>
 */
public class InlayHintProvider {

    private InlayHintProvider() {}

    /**
     * Compute inlay hints for the given document.
     *
     * @param params  the LSP inlay-hint request parameters
     * @param content the current source text of the document
     * @param cache   the AST cache to look up the attributed AST
     * @return list of inlay hints (never null; empty if no hints or no cached AST)
     */
    /**
     * If the hover position falls on a {@code var}-declared variable in the cached AST,
     * return a string of the form {@code ": TypeName"}.  Returns {@code null} if the
     * position is not on a {@code var} declaration or no AST is cached.
     *
     * @param uri     document URI
     * @param content current source text
     * @param line    zero-based line of the hover position
     * @param col     zero-based column of the hover position
     * @param cache   AST cache
     */
    public static String findVarTypeAtPosition(String uri, String content,
                                               int line, int col,
                                               ASTCache cache) {
        ASTCache.Entry entry = cache.get(uri);
        if (entry == null || entry.ast() == null || content == null) return null;

        String filePackage = "";
        if (entry.ast().packge != null) {
            String pkg = entry.ast().packge.toString();
            if (!pkg.isEmpty() && !pkg.startsWith("<")) filePackage = pkg;
        }

        int hoverOffset = DefinitionFinder.lineColToOffset(content, line, col);
        if (hoverOffset < 0) return null;

        // Walk the AST to find a var-declared variable whose name span contains the offset.
        String[] result = { null };
        final String fp = filePackage;
        new JmlTreeScanner() {
            @Override
            public void visitVarDef(com.sun.tools.javac.tree.JCTree.JCVariableDecl tree) {
                super.visitVarDef(tree);
                if (result[0] != null) return;
                if (tree.type == null || tree.type.isErroneous()) return;
                if (!tree.declaredUsingVar()) return;
                int nameEnd   = tree.pos + tree.name.length();
                // Scan backwards from the name to find the 'var' keyword start,
                // skipping any whitespace between 'var' and the variable name.
                int varStart = tree.pos;
                while (varStart > 0 && (content.charAt(varStart - 1) == ' '
                        || content.charAt(varStart - 1) == '\t')) {
                    varStart--;
                }
                if (varStart >= 3
                        && content.regionMatches(varStart - 3, "var", 0, 3)) {
                    varStart -= 3;
                }
                if (hoverOffset >= varStart && hoverOffset <= nameEnd) {
                    result[0] = ": " + shortTypeName(tree.type, fp);
                }
            }
        }.scan(entry.ast());
        return result[0];
    }

    public static List<InlayHint> compute(InlayHintParams params,
                                          String content,
                                          ASTCache cache,
                                          boolean suppressJavaVars) {
        String uri = params.getTextDocument().getUri();
        ASTCache.Entry entry = cache.get(uri);
        if (entry == null || entry.ast() == null || content == null) return List.of();

        // Derive the file's own package string to strip from type names.
        String filePackage = "";
        if (entry.ast().packge != null) {
            String pkg = entry.ast().packge.toString();
            // "unnamed package" is represented as empty or "<unnamed>"
            if (!pkg.isEmpty() && !pkg.startsWith("<")) filePackage = pkg;
        }

        Utils utils = Utils.instance(entry.context());
        List<InlayHint> hints = new ArrayList<>();
        new VarTypeScanner(content, hints, filePackage, suppressJavaVars, utils).scan(entry.ast());
        return hints;
    }

    // -----------------------------------------------------------------------
    // AST scanner
    // -----------------------------------------------------------------------

    private static final class VarTypeScanner extends JmlTreeScanner {

        private final String source;
        private final List<InlayHint> hints;
        private final String filePackage;
        private final boolean suppressJavaVars;
        private final Utils utils;

        VarTypeScanner(String source, List<InlayHint> hints, String filePackage,
                       boolean suppressJavaVars, Utils utils) {
            this.source           = source;
            this.hints            = hints;
            this.filePackage      = filePackage;
            this.suppressJavaVars = suppressJavaVars;
            this.utils            = utils;
        }

        @Override
        public void visitVarDef(JCVariableDecl tree) {
            super.visitVarDef(tree);

            // Bail out if the resolved type is missing / erroneous.
            if (tree.type == null) return;
            if (tree.type.isErroneous()) return;

            // After attribution, vartype is replaced with a synthetic node at NOPOS
            // (see Attr.setSyntheticVariableType).  Use declaredUsingVar() which is set
            // during parsing and survives attribution.
            if (!tree.declaredUsingVar()) return;

            // In jml-only mode, suppress hints for plain Java var declarations —
            // a co-present Java LS already handles those.  JML ghost/model var
            // declarations are unique to OpenJML and are always emitted.
            if (suppressJavaVars && tree.sym instanceof VarSymbol vs
                    && !utils.isGhostOrModel(vs)) return;

            // Compute offset of the end of the declared variable name.
            // tree.pos is the position of the variable name in the source.
            int nameEnd = tree.pos + tree.name.length();
            int[] lc = DefinitionFinder.offsetToLineCol(source, nameEnd);
            if (lc == null) return;

            InlayHint hint = new InlayHint();
            hint.setPosition(new Position(lc[0], lc[1]));
            hint.setLabel(Either.forLeft(": " + shortTypeName(tree.type, filePackage)));
            hint.setKind(InlayHintKind.Type);
            hint.setPaddingLeft(true);
            hints.add(hint);
        }
    }

    // -----------------------------------------------------------------------
    // Type name formatting
    // -----------------------------------------------------------------------

    /**
     * Return a shortened display string for {@code t}.
     *
     * <p>Strips well-known package prefixes for readability:
     * <ul>
     *   <li>{@code java.lang.} — e.g. {@code java.lang.String} → {@code String}</li>
     *   <li>{@code org.jmlspecs.lang.internal.} — JML built-in types appear as their
     *       keyword form: {@code \bigint}, {@code \real}, etc.</li>
     *   <li>The containing file's own package — types in the same package appear as
     *       simple names.</li>
     * </ul>
     * Replacements are applied everywhere in the string, including inside generic
     * type arguments.
     */
    static String shortTypeName(Type t, String filePackage) {
        String s = t.toString();
        // JML built-in types: org.jmlspecs.lang.internal.bigint → \bigint
        s = s.replace("org.jmlspecs.lang.internal.", "\\");
        // Standard Java types
        s = s.replace("java.lang.", "");
        // Types from the same package as the containing file
        if (filePackage != null && !filePackage.isEmpty()) {
            s = s.replace(filePackage + ".", "");
        }
        return s;
    }
}
