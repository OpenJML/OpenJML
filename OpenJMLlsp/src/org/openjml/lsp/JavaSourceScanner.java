package org.openjml.lsp;

import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.util.ArrayList;
import java.util.List;

/**
 * Locates method and constructor declarations in Java source files via AST walking.
 *
 * <p>Use {@link #findMethodsFromAst(JmlCompilationUnit, String)} when an attributed
 * AST is available from the {@link ASTCache}.  Before the first check completes,
 * callers should return an empty list rather than attempt heuristic fallbacks.
 */
public class JavaSourceScanner {

    /**
     * Immutable description of one method found in a source file.
     *
     * <ul>
     *   <li>{@code name}         — display name (class name for constructors, method name otherwise)</li>
     *   <li>{@code rawName}      — unique per-project FQN from {@code Utils.uniqueSymbolName},
     *       e.g. {@code "com.example.MyClass.add(int,int)"}.  Used as the code-lens method
     *       reference, the per-method ESC tracking key, and the proof-result lookup key.</li>
     *   <li>{@code startLine}    — line of the method declaration (used for code-lens placement)</li>
     *   <li>{@code specStartLine} — first JML {@code //@} annotation line immediately before
     *       the declaration; equals {@code startLine} if there are no spec lines.
     *       Use this as the lower bound when matching diagnostics to a method, because
     *       OpenJML reports verification failures on the spec line, not the declaration.</li>
     *   <li>{@code endLine}      — last line attributed to this method (exclusive of next method's spec)</li>
     * </ul>
     */
    public record MethodInfo(String name, String rawName, int startLine, int specStartLine,
                             int endLine, String sourceUri) {
        /** Convenience: does the given 0-based line fall within this method's full range? */
        public boolean contains(int line) { return line >= specStartLine && line <= endLine; }
    }

    /**
     * Return all method declarations found by walking {@code ast}, ordered by line.
     *
     * <p>Handles nested classes, constructors, and package-private methods correctly.
     * Returns an empty list if {@code ast} or {@code source} is {@code null} (i.e.,
     * before the first check completes).
     *
     * @param ast    attributed compilation unit from the {@link ASTCache}
     * @param source full source text (used to locate JML spec-comment lines above each method)
     */
    public static List<MethodInfo> findMethodsFromAst(JmlCompilationUnit ast, String source) {
        if (ast == null || source == null) return List.of();
        String[] lines = source.split("\\r?\\n", -1);
        MethodLensWalker walker = new MethodLensWalker(ast, lines);
        walker.scan(ast);
        return walker.result;
    }

    // -----------------------------------------------------------------------
    // AST walker for code-lens method discovery
    // -----------------------------------------------------------------------

    private static class MethodLensWalker extends JmlTreeScanner {
        private final JmlCompilationUnit cu;
        private final String cuUri;
        private final String[] lines;
        final List<MethodInfo> result = new ArrayList<>();

        MethodLensWalker(JmlCompilationUnit cu, String[] lines) {
            super(null);   // null context → AST_JML_MODE
            this.cu    = cu;
            this.cuUri = cu.sourcefile != null ? cu.sourcefile.toUri().normalize().toString() : "";
            this.lines = lines;
        }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            // tree.pos < 0: synthetic node (e.g. compiler-inserted default constructor) — no source line to place a lens on.
            // tree.sym == null: partially-resolved node from a file with errors — sym is needed to form the FQN key.
            if (tree.pos < 0 || tree.sym == null) return;
            String rawName = tree.name != null ? tree.name.toString() : "";
            // Skip synthetic methods (<clinit> etc.); keep <init> constructors.
            if (rawName.isEmpty() || (rawName.startsWith("<") && !"<init>".equals(rawName))) return;

            // Display name: class simple name for constructors, method name otherwise.
            String ownerSimple = tree.sym.owner != null
                    ? tree.sym.owner.getSimpleName().toString() : "";
            String name = "<init>".equals(rawName)
                    ? (ownerSimple.isEmpty() ? "<init>" : ownerSimple)
                    : rawName;

            // Proof-result key: canonical FQN from Utils.uniqueSymbolName, which matches
            // the key used by Utils.filter() for --method matching, including local and
            // anonymous classes (e.g. "pkg.Outer.1Local.m(int)").
            String fqnKey = Utils.uniqueSymbolName(tree.sym);

            // Source file: JmlMethodDecl carries the file it was declared in (e.g. a
            // companion .jml file).  Code lenses and markers must go to that file.
            String sourceUri = cuUri;
            if (tree instanceof JmlMethodDecl jm && jm.sourcefile != null) {
                sourceUri = jm.sourcefile.toUri().normalize().toString();
            }

            int startLine = Math.max(0, (int) cu.lineMap.getLineNumber(tree.pos) - 1);
            int endOffset = cu.endPositions != null ? tree.getEndPosition(cu.endPositions) : -1;
            int endLine = (endOffset > tree.pos)
                    ? Math.max(startLine, (int) cu.lineMap.getLineNumber(endOffset) - 1)
                    : startLine;
            // findSpecStart scans lines[] (the .java source); only meaningful for methods
            // declared in the same file.  For companion .jml methods use startLine as-is.
            int specStart = sourceUri.equals(cuUri) ? findSpecStart(lines, startLine) : startLine;
            result.add(new MethodInfo(name, fqnKey, startLine, specStart, endLine, sourceUri));
            // Recurse into the method body so that local classes declared inside are visited.
            super.visitMethodDef(tree);
        }
    }

    // -----------------------------------------------------------------------
    // Shared helper
    // -----------------------------------------------------------------------

    /**
     * Walk backwards from {@code startLine} to find the first consecutive
     * {@code //@} JML spec comment line that immediately precedes the declaration.
     * Returns {@code startLine} if there are no spec lines.
     */
    private static int findSpecStart(String[] lines, int startLine) {
        int specStart = startLine;
        for (int j = startLine - 1; j >= 0; j--) {
            String t = lines[j].trim();
            if (t.startsWith("//@")) specStart = j;
            else if (t.isEmpty() || t.startsWith("//") || t.startsWith("*")
                    || t.startsWith("/*") || t.startsWith("@")) { /* skip */ }
            else break;
        }
        return specStart;
    }
}
