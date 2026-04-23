package org.openjml.lsp;

import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import org.eclipse.lsp4j.DocumentHighlight;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Finds all occurrences of the identifier name under the cursor within the current document.
 *
 * <p>Matching is by <em>identifier name</em>, not by compiler symbol identity.  All AST
 * nodes whose {@code name} field equals the target token are reported, regardless of
 * which symbol they resolve to.  This is the intended LSP behaviour for
 * {@code textDocument/documentHighlight}: highlight every occurrence of the same
 * <em>token</em> in the file so the user can visually track it — rather than restricting
 * to a single scope-resolved symbol (which would be lost if the cursor sat on a shadowed
 * name), or doing a raw text search (which would match inside strings and comments).
 *
 * <p>Name extraction uses the source text around the cursor position, so no AST
 * annotation is required just to find the token name.  The AST walk then finds all
 * {@code JCIdent}, {@code JCFieldAccess}, {@code JCClassDecl}, {@code JCMethodDecl},
 * and {@code JCVariableDecl} nodes with that name.
 *
 * <h3>File scope</h3>
 * <ul>
 *   <li><b>{@code .java} files</b> — only the main Java compilation unit is scanned
 *       (the companion {@code .jml} specs CU, if any, is excluded so results stay within
 *       the current document).</li>
 *   <li><b>{@code .jml} files</b> — only the specs compilation unit is scanned (the main
 *       {@code .java} AST is excluded for the same reason).  The entry is located via the
 *       companion {@code .java} URI since {@code .jml} files are compiled through their
 *       companion and stored in the cache under the companion URI.</li>
 * </ul>
 */
public class DocumentHighlightProvider {

    private DocumentHighlightProvider() {}

    /**
     * Return all identifier occurrences of the token at ({@code line}, {@code col}) in
     * the document identified by {@code uri}.
     *
     * @param uri              the document URI ({@code .java} or {@code .jml})
     * @param line             0-indexed cursor line
     * @param col              0-indexed cursor column
     * @param openContent      live in-memory content map (URI → source text)
     * @param cache            the shared AST cache
     * @param companionJavaUri the companion {@code .java} URI (fallback for {@code .jml}
     *                         files when the specs CU is not yet cached under the
     *                         {@code .jml} URI); {@code null} when {@code uri} is a
     *                         {@code .java} file
     * @return list of highlights (never {@code null}, may be empty)
     */
    public static List<DocumentHighlight> findHighlights(
            String uri, int line, int col,
            Map<String, String> openContent,
            ASTCache cache,
            String companionJavaUri) {

        String source = openContent.get(uri);
        if (source == null) return List.of();

        // 1. Extract the identifier token at the cursor from the raw source.
        String targetName = nameAtCursor(source, line, col);
        if (targetName == null) return List.of();

        // 2. Determine scan mode.
        //    .jml files must be scanned in AST_JML_MODE so that JML clause nodes
        //    (requires/ensures/…) are visited.  .java files use AST_JAVA_MODE so that
        //    the companion specs CU is excluded and results stay within the document.
        boolean isJml = uri.endsWith(".jml");

        // 3. Locate the compilation unit to scan.
        //    After a --check, CheckRunner.cacheSpecsCu stores the specs CU directly
        //    under the .jml URI in the live cache, so cache.get(jmlUri) returns it.
        //    The companionJavaUri path is a fallback for when that hasn't happened yet.
        JmlCompilationUnit cuToScan;

        if (isJml) {
            // Primary: specs CU cached under its own .jml URI.
            ASTCache.Entry direct = cache.getNav(uri);
            if (direct == null) direct = cache.get(uri);
            if (direct != null) {
                cuToScan = direct.ast();
            } else if (companionJavaUri != null) {
                // Fallback: companion .java entry with specs CU attached.
                ASTCache.Entry e = cache.getNav(companionJavaUri);
                if (e == null) e = cache.get(companionJavaUri);
                if (e == null) return List.of();
                JmlCompilationUnit specs = e.ast().specsCompilationUnit;
                if (specs == null || specs == e.ast()) return List.of();
                cuToScan = specs;
            } else {
                return List.of();
            }
        } else {
            // .java file: use the file's own main CU (specs CU excluded).
            ASTCache.Entry e = cache.getNav(uri);
            if (e == null) e = cache.get(uri);
            if (e == null) return List.of();
            cuToScan = e.ast();
        }

        // 4. Walk the chosen CU and collect every node whose name matches.
        List<DocumentHighlight> results = new ArrayList<>();
        new NameCollector(targetName, source, results).scanDocument(cuToScan, isJml);
        return results;
    }

    // -----------------------------------------------------------------------
    // Token extraction
    // -----------------------------------------------------------------------

    /**
     * Return the Java identifier token at ({@code line}, {@code col}) in {@code source},
     * or {@code null} if the cursor is not positioned on an identifier character.
     *
     * <p>Expands left and right from the cursor offset while characters satisfy
     * {@link Character#isJavaIdentifierPart}.  Tokens that start with a digit (numeric
     * literals) are rejected because they are not identifier tokens even though their
     * characters are legal identifier parts after the first character.
     */
    static String nameAtCursor(String source, int line, int col) {
        int offset = DefinitionFinder.lineColToOffset(source, line, col);
        if (offset < 0) return null;
        // Clamp to last character when cursor is at EOF.
        if (offset >= source.length()) {
            if (source.isEmpty()) return null;
            offset = source.length() - 1;
        }
        if (!Character.isJavaIdentifierPart(source.charAt(offset))) return null;
        int start = offset;
        while (start > 0 && Character.isJavaIdentifierPart(source.charAt(start - 1))) start--;
        int end = offset + 1;
        while (end < source.length() && Character.isJavaIdentifierPart(source.charAt(end))) end++;
        String name = source.substring(start, end);
        // Reject numeric literals (e.g. "42") which start with a digit.
        if (!Character.isJavaIdentifierStart(name.charAt(0))) return null;
        return name;
    }

    // -----------------------------------------------------------------------
    // AST scanner
    // -----------------------------------------------------------------------

    private static final class NameCollector extends JmlTreeScanner {

        private final String targetName;
        private final String source;
        private final List<DocumentHighlight> results;

        NameCollector(String targetName, String source, List<DocumentHighlight> results) {
            this.targetName = targetName;
            this.source     = source;
            this.results    = results;
        }

        /**
         * Entry point.  For {@code .java} files ({@code jmlOnly=false}) the CU is visited
         * in {@code AST_JAVA_MODE} so the companion specs CU clauses are not double-counted.
         * For {@code .jml} files ({@code jmlOnly=true}) the specs CU is visited in
         * {@code AST_JML_MODE} so JML clauses are included.
         */
        void scanDocument(JmlCompilationUnit cu, boolean jmlOnly) {
            if (jmlOnly) {
                scanMode = AST_JML_MODE;
                scan(cu);
            } else {
                // Mirror RefCollector.scanCU: use AST_JAVA_MODE when a separate specs CU
                // exists to avoid double-counting JML type-spec clauses that appear in
                // both tree.defs and typeSpecs.clauses.
                if (cu.specsCompilationUnit == cu) {
                    scan(cu);
                } else {
                    scanMode = AST_JAVA_MODE;
                    scan(cu);
                }
            }
        }

        // --- use sites (JCIdent and JCFieldAccess) ---

        @Override
        public void visitIdent(JCIdent tree) {
            if (tree.name != null && targetName.equals(tree.name.toString()) && tree.pos >= 0) {
                addHighlight(tree.pos, targetName.length());
            }
            super.visitIdent(tree);
        }

        @Override
        public void visitSelect(JCFieldAccess tree) {
            if (tree.name != null && targetName.equals(tree.name.toString())
                    && tree.pos >= 0) {
                // tree.pos points to the start of the receiver; the selector name follows
                // the last '.'.  Search forward for ".<name>" within a reasonable window.
                String dotName = "." + targetName;
                int limit  = Math.min(tree.pos + 1000, source.length());
                int dotPos = source.indexOf(dotName, tree.pos);
                if (dotPos >= 0 && dotPos < limit) {
                    addHighlight(dotPos + 1, targetName.length());
                }
            }
            super.visitSelect(tree);
        }

        // --- declaration sites ---

        /**
         * Handles class declarations and scans the class body directly via
         * {@code tree.defs} — bypassing {@link JmlTreeScanner#visitClassDef}'s extra
         * {@code typeSpecs.clauses} scan which would double-count JML invariant nodes.
         */
        @Override
        public void visitClassDef(JCClassDecl tree) {
            if (tree.name != null && targetName.equals(tree.name.toString())
                    && tree.pos >= 0 && !tree.name.isEmpty()) {
                addDeclHighlight(tree.name.toString(), tree.pos);
            }
            scan(tree.mods);
            scan(tree.typarams);
            scan(tree.extending);
            scan(tree.implementing);
            scan(tree.defs);
        }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            if (tree.name != null && targetName.equals(tree.name.toString())
                    && tree.pos >= 0
                    && !tree.name.toString().equals("<init>")) {
                addDeclHighlight(tree.name.toString(), tree.pos);
            }
            super.visitMethodDef(tree);
        }

        @Override
        public void visitVarDef(JCVariableDecl tree) {
            if (tree.name != null && targetName.equals(tree.name.toString())
                    && tree.pos >= 0) {
                addDeclHighlight(tree.name.toString(), tree.pos);
            }
            super.visitVarDef(tree);
        }

        // --- helpers ---

        /**
         * Find and add a highlight for the declaration name starting near {@code fromPos}.
         * Scans forward up to 200 characters for the name as a whole-word token (no adjacent
         * identifier characters on either side).
         */
        private void addDeclHighlight(String word, int fromPos) {
            int pos = fromPos;
            int end = Math.min(fromPos + 200, source.length());
            while (pos < end) {
                int found = source.indexOf(word, pos);
                if (found < 0 || found >= end) return;
                boolean beforeOk = found == 0
                        || !Character.isJavaIdentifierPart(source.charAt(found - 1));
                boolean afterOk  = (found + word.length() >= source.length())
                        || !Character.isJavaIdentifierPart(source.charAt(found + word.length()));
                if (beforeOk && afterOk) {
                    addHighlight(found, word.length());
                    return;
                }
                pos = found + 1;
            }
        }

        private void addHighlight(int charOffset, int nameLen) {
            if (charOffset < 0 || charOffset + nameLen > source.length()) return;
            int[] s = DefinitionFinder.offsetToLineCol(source, charOffset);
            int[] e = DefinitionFinder.offsetToLineCol(source, charOffset + nameLen);
            results.add(new DocumentHighlight(
                    new Range(new Position(s[0], s[1]), new Position(e[0], e[1]))));
        }
    }
}
