package org.openjml.lsp;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
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

        // Try JCIdent first (simple name), then JCFieldAccess (a field — cursor on field).
        // Only scan specsCompilationUnit when the cursor is already in a .jml file:
        // specsCompilationUnit positions are in .jml coordinate space, not .java coordinate space.
        NodeMatch match = findNodeAt(entry.ast(), targetOffset, source, uri.endsWith(".jml"));
        if (match == null || match.sym() == null) return null;

        ASTCache.SymbolLocation decl = cache.getDeclarationLocation(match.sym());
        if (decl == null) return null;

        // For the declaration source, prefer the actual file content (AST or disk)
        // over openContent.  openContent may contain synthetic redirections (e.g.
        // the .jml-to-javaUri mapping used for cursor lookup) that would corrupt
        // the offset-to-line/col conversion for the declaration file.
        String declSource = getSource(decl.uri(), cache);
        if (declSource == null) declSource = openContent.get(decl.uri());
        if (declSource == null) return null;

        int[] lc = offsetToLineCol(declSource, decl.charOffset());
        var pos = new Position(lc[0], lc[1]);
        return new Location(decl.uri(), new Range(pos, pos));
    }

    /**
     * Find the {@code Symbol} at ({@code line}, {@code col}) in the given URI's
     * cached AST.  Used by {@link ReferenceFinder} to obtain the target symbol
     * before scanning all cached ASTs for its uses.
     *
     * @return the resolved Symbol, or {@code null} if the cursor is not on a
     *         recognized identifier node
     */
    static com.sun.tools.javac.code.Symbol findSymbolAt(
            String uri, int line, int col,
            Map<String, String> openContent, ASTCache cache) {
        ASTCache.Entry entry = cache.get(uri);
        if (entry == null) return null;

        String source = openContent.get(uri);
        if (source == null) source = readFromAst(entry);
        if (source == null) return null;

        int targetOffset = lineColToOffset(source, line, col);
        if (targetOffset < 0) return null;

        NodeMatch match = findNodeAt(entry.ast(), targetOffset, source, uri.endsWith(".jml"));
        return match != null ? match.sym() : null;
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
                                        int targetOffset, String source,
                                        boolean scanSpecs) {
        IdentFinder finder = new IdentFinder(targetOffset, source);
        finder.scan(ast);
        if (scanSpecs) {
            JmlCompilationUnit cu = ast.specsCompilationUnit;
            if (cu != null && cu != ast) finder.scan(cu);
        }
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

        /**
         * Find {@code word} as a whole identifier (word-boundary check) in
         * {@code source} between {@code from} and {@code from + limit}.
         * Returns the character offset, or -1 if not found.
         */
        private int findDeclName(String word, int from, int limit) {
            int pos = from;
            int end = Math.min(from + limit, source.length());
            while (pos < end) {
                int found = source.indexOf(word, pos);
                if (found < 0 || found >= end) return -1;
                boolean beforeOk = found == 0
                        || !Character.isJavaIdentifierPart(source.charAt(found - 1));
                boolean afterOk = found + word.length() >= source.length()
                        || !Character.isJavaIdentifierPart(source.charAt(found + word.length()));
                if (beforeOk && afterOk) return found;
                pos = found + 1;
            }
            return -1;
        }

        /** Check whether {@code targetOffset} falls within [{@code namePos}, {@code namePos+len}]. */
        private boolean cursorOn(int namePos, int len) {
            return namePos >= 0 && namePos <= targetOffset && targetOffset <= namePos + len;
        }

        @Override
        public void visitClassDef(com.sun.tools.javac.tree.JCTree.JCClassDecl tree) {
            // Handle cursor on the class name in its own declaration:
            //   public class Foo { ... }  or  //@ model public class Bar {}
            if (tree.pos >= 0 && tree.name != null && tree.sym != null) {
                String nameStr = tree.name.toString();
                if (!nameStr.isEmpty()) {
                    int namePos = findDeclName(nameStr, tree.pos, 200);
                    if (cursorOn(namePos, nameStr.length())) {
                        best = new NodeMatch(tree.sym);
                    }
                }
            }
            super.visitClassDef(tree);
        }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            // Handle cursor on the method name in its own declaration.
            if (tree.pos >= 0 && tree.sym != null && tree.name != null
                    && !tree.name.toString().equals("<init>")) {
                String nameStr = tree.name.toString();
                int namePos = findDeclName(nameStr, tree.pos, 200);
                if (cursorOn(namePos, nameStr.length())) {
                    best = new NodeMatch(tree.sym);
                }
            }
            super.visitMethodDef(tree);
            if (tree instanceof JmlMethodDecl jmlMethod && jmlMethod.methodSpecs != null) {
                scan(jmlMethod.methodSpecs.cases);
            }
        }

        @Override
        public void visitVarDef(com.sun.tools.javac.tree.JCTree.JCVariableDecl tree) {
            // Handle cursor on the variable/field/parameter name in its own declaration.
            if (tree.pos >= 0 && tree.sym != null && tree.name != null) {
                String nameStr = tree.name.toString();
                if (!nameStr.isEmpty()) {
                    int namePos = findDeclName(nameStr, tree.pos, 300);
                    if (cursorOn(namePos, nameStr.length())) {
                        best = new NodeMatch(tree.sym);
                    }
                }
            }
            super.visitVarDef(tree);
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
                String fieldName = tree.name.toString();
                int nameLen = fieldName.length();
                // Scan backward from the cursor to find the start of the identifier
                // that is under the cursor.  Stop at tree.pos so we never walk
                // into a different expression.
                int nameStart = targetOffset;
                while (nameStart > tree.pos && nameStart > 0
                        && Character.isJavaIdentifierPart(source.charAt(nameStart - 1))) {
                    nameStart--;
                }
                // The character immediately before must be '.', and the text starting
                // at nameStart must equal tree.name (guards against false matches on
                // nested field accesses like a.b.c where the outer node has name=c
                // but the cursor is on b).
                if (nameStart > 0 && source.charAt(nameStart - 1) == '.'
                        && nameStart + nameLen <= source.length()
                        && source.regionMatches(nameStart, fieldName, 0, nameLen)
                        && targetOffset <= nameStart + nameLen) {
                    best = new NodeMatch(tree.sym);
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
