package org.openjml.lsp;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import org.eclipse.lsp4j.DocumentSymbol;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.SymbolKind;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import java.util.ArrayList;
import java.util.List;

/**
 * Produces a hierarchical {@link DocumentSymbol} tree from a Java/JML source file.
 *
 * <p>Used for {@code textDocument/documentSymbol} (the VS Code Outline panel).
 *
 * <p>Top-level classes are roots; their fields, constructors, methods, and nested
 * classes are children.  JML ghost/model declarations (which live inside JML
 * comment regions) and synthetic names are omitted.
 *
 * <p>Full ranges use the AST's end-position table ({@link JmlCompilationUnit#endPositions});
 * selection ranges (the highlighted portion when the symbol is selected in the outline)
 * locate the identifier name with a short forward scan from the node start position.
 */
public class DocumentSymbolProvider {

    /**
     * Build a document-symbol tree for {@code ast}.
     *
     * @param ast    attributed {@link JmlCompilationUnit} from the {@link ASTCache}
     * @param source full source text (for offset → line/col conversion)
     * @return top-level symbols (classes, enums, interfaces) with children
     */
    public static List<DocumentSymbol> fromAst(JmlCompilationUnit ast, String source) {
        int[] lineOffsets = buildLineOffsets(source);
        List<DocumentSymbol> roots = new ArrayList<>();
        for (JCTree def : ast.defs) {
            if (def instanceof JCClassDecl cd) {
                DocumentSymbol sym = classSymbol(cd, ast, source, lineOffsets);
                if (sym != null) roots.add(sym);
            }
        }
        return roots;
    }

    // -----------------------------------------------------------------------
    // Builders
    // -----------------------------------------------------------------------

    private static DocumentSymbol classSymbol(JCClassDecl cd, JmlCompilationUnit ast,
                                               String source, int[] lineOffsets) {
        if (cd.name == null || cd.pos < 0) return null;
        String name = cd.name.toString();
        if (name.isEmpty()) return null;

        SymbolKind kind;
        if (cd.sym != null) {
            if (cd.sym.isEnum())           kind = SymbolKind.Enum;
            else if (cd.sym.isInterface()) kind = SymbolKind.Interface;
            else                           kind = SymbolKind.Class;
        } else {
            kind = SymbolKind.Class;
        }

        Range range    = fullRange(cd, ast, source, lineOffsets);
        Range selRange = nameRange(cd.pos, name, source, lineOffsets);

        DocumentSymbol sym = new DocumentSymbol(name, kind, range, selRange);

        List<DocumentSymbol> children = new ArrayList<>();
        for (JCTree member : cd.defs) {
            if (member instanceof JCMethodDecl md) {
                DocumentSymbol ms = methodSymbol(md, cd, ast, source, lineOffsets);
                if (ms != null) children.add(ms);
            } else if (member instanceof JCVariableDecl vd) {
                DocumentSymbol fs = fieldSymbol(vd, ast, source, lineOffsets);
                if (fs != null) children.add(fs);
            } else if (member instanceof JCClassDecl nested) {
                DocumentSymbol ns = classSymbol(nested, ast, source, lineOffsets);
                if (ns != null) children.add(ns);
            }
        }
        if (!children.isEmpty()) sym.setChildren(children);
        return sym;
    }

    private static DocumentSymbol methodSymbol(JCMethodDecl md, JCClassDecl owner,
                                                JmlCompilationUnit ast,
                                                String source, int[] lineOffsets) {
        // Skip JML ghost/model method declarations.
        if (md instanceof JmlMethodDecl jmlMd && jmlMd.isJML()) return null;
        if (md.pos < 0) return null;

        String rawName = md.name != null ? md.name.toString() : "";
        // Constructors have the synthetic name <init>; display using the class name.
        boolean isCtor = "<init>".equals(rawName);
        // Skip static initializers (<clinit>) and other synthetics.
        if (!isCtor && (rawName.isEmpty() || rawName.startsWith("<"))) return null;

        String name = isCtor ? owner.name.toString() : rawName;
        SymbolKind kind = isCtor ? SymbolKind.Constructor : SymbolKind.Method;
        Range range    = fullRange(md, ast, source, lineOffsets);
        Range selRange = nameRange(md.pos, name, source, lineOffsets);
        return new DocumentSymbol(name, kind, range, selRange);
    }

    private static DocumentSymbol fieldSymbol(JCVariableDecl vd, JmlCompilationUnit ast,
                                               String source, int[] lineOffsets) {
        // Skip JML ghost/model field declarations.
        if (vd instanceof JmlVariableDecl jmlVd && jmlVd.isJML()) return null;
        if (vd.name == null || vd.pos < 0) return null;
        String name = vd.name.toString();
        // Skip synthetic captures (e.g. this$0 in inner classes).
        if (name.isEmpty() || name.startsWith("this$") || name.startsWith("val$")) return null;

        Range range    = fullRange(vd, ast, source, lineOffsets);
        Range selRange = nameRange(vd.pos, name, source, lineOffsets);
        return new DocumentSymbol(name, SymbolKind.Field, range, selRange);
    }

    // -----------------------------------------------------------------------
    // Range helpers
    // -----------------------------------------------------------------------

    /**
     * The full extent of a tree node, from its start position to the end
     * recorded in the compilation unit's end-position table.  Falls back to
     * a point range at the start if the end is unavailable.
     */
    private static Range fullRange(JCTree tree, JmlCompilationUnit ast,
                                   String source, int[] lineOffsets) {
        Position start = offsetToPos(tree.pos, lineOffsets);
        int endOffset  = ast.endPositions != null
                ? tree.getEndPosition(ast.endPositions) : -1;
        Position end = (endOffset > tree.pos)
                ? offsetToPos(endOffset, lineOffsets)
                : start;
        return new Range(start, end);
    }

    /**
     * Locate the identifier {@code name} in the source text starting from
     * {@code nodePos} and return its character range.  A forward scan of at
     * most 300 characters is performed; the first whole-identifier match is
     * used.  Falls back to a point range at {@code nodePos} if not found.
     */
    private static Range nameRange(int nodePos, String name, String source, int[] lineOffsets) {
        int searchEnd = Math.min(nodePos + 300, source.length() - name.length());
        for (int i = nodePos; i <= searchEnd; i++) {
            if (source.startsWith(name, i)) {
                // Must be a whole identifier (not a prefix/suffix of another word).
                boolean okBefore = i == 0
                        || !Character.isJavaIdentifierPart(source.charAt(i - 1));
                boolean okAfter  = (i + name.length() >= source.length())
                        || !Character.isJavaIdentifierPart(source.charAt(i + name.length()));
                if (okBefore && okAfter) {
                    return new Range(offsetToPos(i, lineOffsets),
                                     offsetToPos(i + name.length(), lineOffsets));
                }
            }
        }
        // Fallback: point range at node position.
        Position p = offsetToPos(nodePos, lineOffsets);
        return new Range(p, p);
    }

    // -----------------------------------------------------------------------
    // Offset ↔ Position
    // -----------------------------------------------------------------------

    private static Position offsetToPos(int offset, int[] lineOffsets) {
        if (offset <= 0) return new Position(0, 0);
        int lo = 0, hi = lineOffsets.length - 1;
        while (lo < hi) {
            int mid = (lo + hi + 1) / 2;
            if (lineOffsets[mid] <= offset) lo = mid;
            else hi = mid - 1;
        }
        return new Position(lo, offset - lineOffsets[lo]);
    }

    private static int[] buildLineOffsets(String source) {
        List<Integer> list = new ArrayList<>();
        list.add(0);
        for (int i = 0; i < source.length(); i++) {
            if (source.charAt(i) == '\n') list.add(i + 1);
        }
        int[] arr = new int[list.size()];
        for (int i = 0; i < arr.length; i++) arr[i] = list.get(i);
        return arr;
    }

    private DocumentSymbolProvider() {}
}
