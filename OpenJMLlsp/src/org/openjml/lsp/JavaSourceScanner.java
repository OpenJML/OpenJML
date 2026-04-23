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
 * <p>Use {@link #findMethodsFromAst(JmlCompilationUnit)} when an attributed
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
     *   <li>{@code specStartLine} — equals {@code startLine} (the method declaration's AST
     *       start position).  Used as the lower bound when matching diagnostics to a method.</li>
     *   <li>{@code bodyStartLine} — 0-based line of the opening {@code {}} of the method body;
     *       equals {@code endLine} for abstract/interface methods with no body.</li>
     *   <li>{@code endLine}      — last line attributed to this method (exclusive of next method's spec)</li>
     * </ul>
     */
    public record MethodInfo(String name, String rawName, int startLine, int specStartLine,
                             int bodyStartLine, int endLine, String sourceUri) {
        /** Convenience: does the given 0-based line fall within this method's full range? */
        public boolean contains(int line) { return line >= specStartLine && line <= endLine; }
        /** True if {@code line} is on the spec comments or method signature (before the body). */
        public boolean onSignature(int line) { return line >= specStartLine && line <= bodyStartLine; }
    }

    /**
     * Return all method declarations found by walking {@code ast}, ordered by line.
     *
     * <p>Handles nested classes, constructors, and package-private methods correctly.
     * Returns an empty list if {@code ast} is {@code null} (i.e., before the first
     * check completes).  Code-lens position is taken from the method declaration's
     * AST start position ({@code specStartLine} equals {@code startLine}).
     *
     * @param ast attributed compilation unit from the {@link ASTCache}
     */
    public static List<MethodInfo> findMethodsFromAst(JmlCompilationUnit ast) {
        if (ast == null) return List.of();
        MethodLensWalker walker = new MethodLensWalker(ast);
        walker.scan(ast);
        return walker.result;
    }

    // -----------------------------------------------------------------------
    // AST walker for code-lens method discovery
    // -----------------------------------------------------------------------

    private static class MethodLensWalker extends JmlTreeScanner {
        private final JmlCompilationUnit cu;
        private final String cuUri;
        final List<MethodInfo> result = new ArrayList<>();

        MethodLensWalker(JmlCompilationUnit cu) {
            super(null);   // null context → AST_JML_MODE
            this.cu    = cu;
            this.cuUri = cu.sourcefile != null ? cu.sourcefile.toUri().normalize().toString() : "";
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
            int bodyStart = (tree.body != null && tree.body.pos > tree.pos)
                    ? Math.max(startLine, (int) cu.lineMap.getLineNumber(tree.body.pos) - 1)
                    : endLine;
            result.add(new MethodInfo(name, fqnKey, startLine, startLine, bodyStart, endLine, sourceUri));
            // Recurse into the method body so that local classes declared inside are visited.
            super.visitMethodDef(tree);
        }
    }

}
