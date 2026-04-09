package org.openjml.lsp;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Finds all source locations that reference a given symbol.
 *
 * <p>Algorithm:
 * <ol>
 *   <li>Resolve the symbol at the cursor using {@link DefinitionFinder#findSymbolAt}.</li>
 *   <li>Walk every cached AST and collect every {@code JCIdent}, {@code JCFieldAccess},
 *       {@code JCClassDecl}, {@code JCMethodDecl}, and {@code JCVariableDecl} node
 *       whose {@code sym} field is the same object ({@code ==}) as the target symbol.</li>
 *   <li>Convert each matched character offset to an LSP {@link Location}.</li>
 * </ol>
 *
 * <p>Symbol identity ({@code ==}) is correct within a single IAPI compilation context:
 * javac reuses the same {@link Symbol} instance for every reference to a given declaration.
 * Cross-context symbols are not matched — references in files compiled in a different
 * {@code IAPI} invocation are not returned.
 */
public class ReferenceFinder {

    private ReferenceFinder() {}

    /**
     * Find all references to the symbol at ({@code line}, {@code col}) in {@code uri}.
     *
     * @param uri                the document URI where the cursor is
     * @param line               0-indexed line number
     * @param col                0-indexed column number
     * @param openContent        map of URI → source text for all open documents
     * @param cache              the shared AST cache
     * @param includeDeclaration if {@code true}, include the symbol's own declaration site
     * @return list of reference locations (may be empty, never {@code null})
     */
    public static List<Location> findReferences(
            String uri, int line, int col,
            Map<String, String> openContent,
            ASTCache cache,
            boolean includeDeclaration) {

        Symbol sym = DefinitionFinder.findSymbolAt(uri, line, col, openContent, cache);
        if (sym == null) return List.of();

        List<Location> results = new ArrayList<>();

        cache.forEachNav((entryUri, entry) -> {
            String src = openContent.get(entryUri);
            if (src == null) {
                try { src = entry.ast().sourcefile.getCharContent(false).toString(); }
                catch (IOException e) { return; }
            }
            new RefCollector(sym, entryUri, src, includeDeclaration, results)
                    .scan(entry.ast());
        });

        return results;
    }

    // -----------------------------------------------------------------------
    // AST scanner
    // -----------------------------------------------------------------------

    private static class RefCollector extends JmlTreeScanner {
        private final Symbol targetSym;
        private final String uri;
        private final String source;
        private final boolean includeDeclaration;
        private final List<Location> results;

        RefCollector(Symbol sym, String uri, String source,
                     boolean includeDeclaration, List<Location> results) {
            this.targetSym         = sym;
            this.uri               = uri;
            this.source            = source;
            this.includeDeclaration = includeDeclaration;
            this.results           = results;
        }

        // --- use sites (JCIdent and JCFieldAccess) ---

        @Override
        public void visitIdent(JCIdent tree) {
            if (tree.sym == targetSym && tree.pos >= 0) {
                addLocation(tree.pos, tree.name.toString().length());
            }
            super.visitIdent(tree);
        }

        @Override
        public void visitSelect(JCFieldAccess tree) {
            if (tree.sym == targetSym && tree.pos >= 0 && tree.name != null) {
                String dotName = "." + tree.name.toString();
                int limit = Math.min(tree.pos + 1000, source.length());
                int dotPos = source.indexOf(dotName, tree.pos);
                if (dotPos >= 0 && dotPos < limit) {
                    addLocation(dotPos + 1, tree.name.toString().length());
                }
            }
            super.visitSelect(tree);
        }

        // --- declaration sites (only when includeDeclaration is true) ---

        /**
         * Handles class declaration sites ({@code includeDeclaration}) and scans
         * the class body ({@code tree.defs}) directly — bypassing
         * {@link JmlTreeScanner#visitClassDef}'s additional {@code typeSpecs.clauses}
         * scan, which would double-count JML invariant nodes already present in
         * {@code tree.defs}.
         *
         * <p>JML invariants declared in a file are stored as {@code JmlTypeClause}
         * nodes in the class's {@code defs} list (scanned via {@code scan(tree.defs)})
         * AND also in {@code typeSpecs.clauses} (a summary convenience field).
         * Scanning both causes each invariant to be reported twice.  Method specs
         * are still found because {@code visitMethodDef} runs in
         * {@link JmlTreeScanner#AST_JML_MODE} and scans {@code methodSpecs}.
         */
        @Override
        public void visitClassDef(JCClassDecl tree) {
            if (includeDeclaration && tree.sym == targetSym
                    && tree.pos >= 0 && tree.name != null) {
                String nameStr = tree.name.toString();
                if (!nameStr.isEmpty()) {
                    int namePos = findWordInSource(nameStr, tree.pos, tree.pos + 200);
                    if (namePos >= 0) addLocation(namePos, nameStr.length());
                }
            }
            // Scan class body directly (tree.defs) without going through
            // JmlTreeScanner.visitClassDef, which also scans typeSpecs.clauses.
            scan(tree.mods);
            scan(tree.typarams);
            scan(tree.extending);
            scan(tree.implementing);
            scan(tree.defs);
        }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            if (includeDeclaration && tree.sym == targetSym
                    && tree.pos >= 0 && tree.name != null
                    && !tree.name.toString().equals("<init>")) {
                String nameStr = tree.name.toString();
                int namePos = findWordInSource(nameStr, tree.pos, tree.pos + 200);
                if (namePos >= 0) addLocation(namePos, nameStr.length());
            }
            super.visitMethodDef(tree);
        }

        @Override
        public void visitVarDef(JCVariableDecl tree) {
            if (includeDeclaration && tree.sym == targetSym
                    && tree.pos >= 0 && tree.name != null) {
                String nameStr = tree.name.toString();
                int namePos = findWordInSource(nameStr, tree.pos, tree.pos + 200);
                if (namePos >= 0) addLocation(namePos, nameStr.length());
            }
            super.visitVarDef(tree);
        }

        // --- helpers ---

        /**
         * Find {@code word} as a standalone identifier in {@code source} between
         * {@code from} (inclusive) and {@code limit} (exclusive).  A "standalone"
         * match is one where neither the preceding nor the following character is a
         * Java identifier part, preventing false matches on substrings.
         */
        private int findWordInSource(String word, int from, int limit) {
            int pos = from;
            int end = Math.min(limit, source.length());
            while (pos < end) {
                int found = source.indexOf(word, pos);
                if (found < 0 || found >= end) return -1;
                boolean beforeOk = found == 0
                        || !Character.isJavaIdentifierPart(source.charAt(found - 1));
                boolean afterOk  = found + word.length() >= source.length()
                        || !Character.isJavaIdentifierPart(source.charAt(found + word.length()));
                if (beforeOk && afterOk) return found;
                pos = found + 1;
            }
            return -1;
        }

        private void addLocation(int charOffset, int nameLen) {
            int[] startLc = DefinitionFinder.offsetToLineCol(source, charOffset);
            int[] endLc   = DefinitionFinder.offsetToLineCol(source, charOffset + nameLen);
            results.add(new Location(uri,
                    new Range(new Position(startLc[0], startLc[1]),
                              new Position(endLc[0],   endLc[1]))));
        }
    }
}
