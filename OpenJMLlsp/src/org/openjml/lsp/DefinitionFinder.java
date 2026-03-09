package org.openjml.lsp;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;

/**
 * Finds the LSP {@link Location} of the declaration for the identifier at a
 * given cursor position in a source file.
 *
 * <p>Algorithm:
 * <ol>
 *   <li>Convert the LSP (line, col) position to a character offset in the source.</li>
 *   <li>Walk the cached, type-attributed AST to find the {@code JCIdent} or
 *       {@code JCFieldAccess} node whose name span contains the target offset.</li>
 *   <li>Look up the resolved symbol in the {@link ASTCache} declaration index.</li>
 *   <li>Convert the declaration's character offset back to an LSP Location.</li>
 * </ol>
 *
 * <p>Works for identifiers resolved within the same IAPI compilation context.
 * Both regular Java identifiers and identifiers appearing inside JML clauses
 * ({@code //@ requires}, {@code //@ ensures}, etc.) are supported, because
 * OpenJML parses JML comments with source-file positions and resolves their
 * symbols during attribution.
 */
public class DefinitionFinder {

    private DefinitionFinder() {}

    /**
     * Find the definition of the identifier at ({@code line}, {@code col}) in
     * {@code uri}.
     *
     * @param uri         the document URI where the cursor is
     * @param line        0-indexed line number
     * @param col         0-indexed column number
     * @param openContent map of URI → source text for all open documents
     *                    (used as the first source for both cursor and declaration files)
     * @param cache       the shared AST cache
     * @return the LSP Location of the declaration, or {@code null} if not found
     */
    public static Location findDefinition(String uri, int line, int col,
                                          Map<String, String> openContent,
                                          ASTCache cache) {
        ASTCache.Entry entry = cache.get(uri);
        if (entry == null) return null;

        String source = openContent.get(uri);
        if (source == null) source = readFromAst(entry);
        if (source == null) return null;

        int targetOffset = lineColToOffset(source, line, col);
        if (targetOffset < 0) return null;

        // Try JCIdent first (simple name), then JCFieldAccess (a.field — cursor on field).
        NodeMatch match = findNodeAt(entry.ast(), targetOffset, source);
        if (match == null || match.sym() == null) return null;

        ASTCache.SymbolLocation decl = cache.getDeclarationLocation(match.sym());
        if (decl == null) return null;

        String declSource = openContent.get(decl.uri());
        if (declSource == null) declSource = getSource(decl.uri(), cache);
        if (declSource == null) return null;

        int[] lc = offsetToLineCol(declSource, decl.charOffset());
        var pos = new Position(lc[0], lc[1]);
        return new Location(decl.uri(), new Range(pos, pos));
    }

    // -----------------------------------------------------------------------
    // Position arithmetic
    // -----------------------------------------------------------------------

    /** Convert 0-indexed (line, col) to a character offset in {@code source}. */
    static int lineColToOffset(String source, int line, int col) {
        int offset = 0;
        int currentLine = 0;
        while (currentLine < line && offset < source.length()) {
            if (source.charAt(offset) == '\n') currentLine++;
            offset++;
        }
        return offset + col;
    }

    /** Convert a character offset to 0-indexed (line, col). */
    public static int[] offsetToLineCol(String source, int offset) {
        int line = 0, col = 0;
        int end = Math.min(offset, source.length());
        for (int i = 0; i < end; i++) {
            if (source.charAt(i) == '\n') { line++; col = 0; }
            else col++;
        }
        return new int[]{line, col};
    }

    // -----------------------------------------------------------------------
    // AST search
    // -----------------------------------------------------------------------

    /** A matched node: the symbol it resolved to. */
    private record NodeMatch(com.sun.tools.javac.code.Symbol sym) {}

    /**
     * Walk the AST to find a {@code JCIdent} or {@code JCFieldAccess} whose
     * name span contains {@code targetOffset}.  Returns the innermost match.
     */
    private static NodeMatch findNodeAt(JmlCompilationUnit ast,
                                        int targetOffset, String source) {
        IdentFinder finder = new IdentFinder(targetOffset, source);
        finder.scan(ast);
        return finder.best;
    }

    private static class IdentFinder extends JmlTreeScanner {
        private final int targetOffset;
        private final String source;
        NodeMatch best = null;

        IdentFinder(int targetOffset, String source) {
            this.targetOffset = targetOffset;
            this.source = source;
        }

        @Override
        public void visitClassDef(com.sun.tools.javac.tree.JCTree.JCClassDecl tree) {
            // Handle cursor on the class name in its own declaration:
            //   public class Foo { ... }  or  //@ model public class Bar {}
            // JCClassDecl has no child JCIdent for the name, so we search the source
            // text forward from tree.pos for the first occurrence of the name.
            if (tree.pos >= 0 && tree.name != null && tree.sym != null) {
                String nameStr = tree.name.toString();
                if (!nameStr.isEmpty()) {
                    int namePos = source.indexOf(nameStr, tree.pos);
                    if (namePos >= 0 && namePos <= tree.pos + 200) {
                        int nameLen = nameStr.length();
                        if (namePos <= targetOffset && targetOffset <= namePos + nameLen) {
                            best = new NodeMatch(tree.sym);
                        }
                    }
                }
            }
            super.visitClassDef(tree);
        }

        @Override
        public void visitIdent(JCIdent tree) {
            if (tree.pos >= 0) {
                int len = tree.name.toString().length();
                if (tree.pos <= targetOffset && targetOffset <= tree.pos + len) {
                    best = new NodeMatch(tree.sym);
                }
            }
            super.visitIdent(tree);
        }

        @Override
        public void visitSelect(JCFieldAccess tree) {
            // For  selected.name , javac stores pos as the start of `selected`.
            // The field name follows the last '.' in the source.
            // Estimate the name position by scanning backwards from the end of
            // the selected expression.
            if (tree.pos >= 0 && tree.name != null && tree.sym != null) {
                int nameLen = tree.name.toString().length();
                // Find the '.' that precedes the field name.
                // tree.pos is start of the full expression; search forward for the last '.'.
                int dotPos = -1;
                for (int i = tree.pos; i < Math.min(tree.pos + 1000, source.length()); i++) {
                    if (source.charAt(i) == '.') dotPos = i;
                    // Stop once we've passed possible positions
                    if (i > targetOffset + nameLen + 2) break;
                }
                if (dotPos >= 0) {
                    int nameStart = dotPos + 1;
                    if (nameStart <= targetOffset && targetOffset <= nameStart + nameLen) {
                        best = new NodeMatch(tree.sym);
                    }
                }
            }
            super.visitSelect(tree);
        }
    }

    // -----------------------------------------------------------------------
    // Source text helpers
    // -----------------------------------------------------------------------

    /** Try to get source text from the AST's JavaFileObject (works for disk files). */
    private static String readFromAst(ASTCache.Entry entry) {
        try {
            return entry.ast().sourcefile.getCharContent(false).toString();
        } catch (IOException e) {
            return null;
        }
    }

    /**
     * Get source text for a declaration URI: try AST cache first (disk files),
     * then fall back to reading from disk.
     */
    private static String getSource(String uri, ASTCache cache) {
        ASTCache.Entry entry = cache.get(uri);
        if (entry != null) {
            String s = readFromAst(entry);
            if (s != null) return s;
        }
        String path = CheckRunner.uriToPath(uri);
        if (path == null) return null;
        try {
            return Files.readString(Path.of(path));
        } catch (IOException e) {
            return null;
        }
    }
}
