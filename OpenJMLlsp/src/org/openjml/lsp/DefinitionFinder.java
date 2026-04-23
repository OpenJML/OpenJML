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
import java.util.Arrays;
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
        ASTCache.Entry entry = cache.getNav(uri);
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
        if (match == null || match.sym() == null) {
            ServerLog.serverLog("[DefinitionFinder] no symbol found at offset " + targetOffset);
            return null;
        }

        com.sun.tools.javac.code.Symbol sym = match.sym();
        ServerLog.serverLog("[DefinitionFinder] symbol=" + sym
                + "  class=" + sym.getClass().getSimpleName()
                + "  owner=" + sym.owner
                + "  ownerClass=" + (sym.owner == null ? "null" : sym.owner.getClass().getSimpleName())
                + "  qualifiedName=" + sym.getQualifiedName());

        ASTCache.SymbolLocation decl = cache.getDeclarationLocation(sym);
        ServerLog.serverLog("[DefinitionFinder] declarationLocation=" + decl);
        if (decl == null) return null;

        // For the declaration source, prefer the actual file content (AST or disk)
        // over openContent.  openContent may contain synthetic redirections (e.g.
        // the .jml-to-javaUri mapping used for cursor lookup) that would corrupt
        // the offset-to-line/col conversion for the declaration file.
        String declSource = getSource(decl.uri(), cache);
        if (declSource == null) declSource = openContent.get(decl.uri());
        if (declSource == null) return null;

        String symName = sym.name.toString();
        int[] startLc = offsetToLineCol(declSource, decl.charOffset());
        int[] endLc   = offsetToLineCol(declSource, decl.charOffset() + symName.length());
        return new Location(decl.uri(), new Range(
                new Position(startLc[0], startLc[1]),
                new Position(endLc[0],   endLc[1])));
    }

    /**
     * Returns a compact, single-line representation of a {@link Location} for logging.
     * Format: {@code filename:line:startChar-endChar} (line is 1-based).
     * Example: {@code A.java:6:14-17}
     */
    public static String locStr(Location loc) {
        if (loc == null) return "null";
        String uri = loc.getUri();
        int slash = Math.max(uri.lastIndexOf('/'), uri.lastIndexOf('\\'));
        String file = slash >= 0 ? uri.substring(slash + 1) : uri;
        Range r = loc.getRange();
        if (r == null) return file;
        Position s = r.getStart(), e = r.getEnd();
        int line = s.getLine() + 1;
        int sc   = s.getCharacter();
        int ec   = e.getCharacter();
        return sc == ec
                ? file + ":" + line + ":" + sc
                : file + ":" + line + ":" + sc + "-" + ec;
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
        ASTCache.Entry entry = cache.getNav(uri);
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
        for (int i = 0; i < line; i++) {
            int next = source.indexOf('\n', offset);
            if (next < 0) return source.length() + col; // line beyond EOF
            offset = next + 1;
        }
        return offset + col;
    }

    /**
     * Lazy line-start index that survives incremental edits.
     *
     * <p>Maintains a growing {@code int[]} where {@code starts[i]} is the
     * character offset of the first character on line {@code i} (0-indexed).
     * Entries are computed on demand; {@link #toOffset} only scans the
     * characters between the last built line and the requested line.
     *
     * <p>After an in-place edit, call {@link #applyEdit} to shift the cached
     * line-start offsets that lie beyond the edited range, and call
     * {@link #rebind} to point the index at the updated source buffer.  This
     * avoids the O(n) {@code StringBuilder.toString()} snapshot that would
     * otherwise be required before each subsequent change in a multi-delta
     * event.
     *
     * <p>For single-change events (the common case) just construct, call
     * {@link #toOffset} twice, and discard.
     */
    static final class LineIndex {
        private CharSequence source;
        private int[] starts;
        private int built; // number of entries stored (starts[0..built-1] are valid)

        LineIndex(CharSequence source) {
            this.source = source;
            // Assumes average line length >= 32 chars (typical for Java source),
            // so (length >> 5) + 1 is a sufficient line-count upper bound.
            // Files with shorter average lines will trigger a resize in toOffset().
            this.starts = new int[Math.max(64, (source.length() >> 5) + 1)];
            this.starts[0] = 0;
            this.built = 1; // line 0 always starts at offset 0
        }

        /** Switch the backing source (e.g. from the original String to a StringBuilder). */
        void rebind(CharSequence newSource) { this.source = newSource; }

        /** Convert 0-indexed (line, col) to a character offset. */
        int toOffset(int line, int col) {
            if (line < built) return starts[line] + col;
            // Grow the starts array if needed.
            if (line >= starts.length)
                starts = Arrays.copyOf(starts, Math.max(starts.length * 2, line + 1));
            int offset = starts[built - 1];
            while (built <= line) {
                int next = indexOfNewline(offset);
                if (next < 0) return source.length() + col; // line beyond EOF
                starts[built++] = next + 1;
                offset = next + 1;
            }
            return offset + col;
        }

        /**
         * Invalidate all cached line-start entries at or after {@code startLine + 1}.
         *
         * <p>After an edit that begins on {@code startLine}, the start offset of
         * {@code startLine} itself ({@code starts[startLine]}) is still valid — it
         * precedes the edit point.  Every subsequent entry is potentially wrong
         * (the replacement text may contain a different number of newlines than
         * the deleted range).  Truncating {@code built} to {@code startLine + 1}
         * causes {@link #toOffset} to lazily rescan from {@code starts[startLine]}
         * through the updated source on the next call.
         */
        void applyEdit(int startLine) {
            built = Math.min(built, startLine + 1);
        }

        /** Fast newline search: uses intrinsic/optimised paths for String and StringBuilder. */
        private int indexOfNewline(int from) {
            if (source instanceof String s)        return s.indexOf('\n', from);
            if (source instanceof StringBuilder sb) return sb.indexOf("\n", from);
            // Generic fallback for any other CharSequence.
            int len = source.length();
            for (int i = from; i < len; i++) if (source.charAt(i) == '\n') return i;
            return -1;
        }
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
        ASTCache.Entry entry = cache.getNav(uri);
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
