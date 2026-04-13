package org.openjml.lsp;

import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Locates method and constructor declarations in Java source files.
 *
 * <p>Two strategies are provided:
 * <ul>
 *   <li>{@link #findMethods(String)} — regex heuristic, works without an AST,
 *       suitable for immediate code-lens placement before the first type-check.</li>
 *   <li>{@link #findMethodsFromAst(JmlCompilationUnit, String)} — AST-based,
 *       precise; use this when an attributed AST is available from the
 *       {@link ASTCache}.</li>
 * </ul>
 *
 * <p>The regex strategy requires at least one explicit access or modifier
 * keyword ({@code public}, {@code private}, {@code protected}, {@code static},
 * etc.) to reduce false positives from method calls and variable declarations.
 * Results are approximate; the AST strategy is preferred when available.
 */
public class JavaSourceScanner {

    /**
     * Immutable description of one method found in a source file.
     *
     * <ul>
     *   <li>{@code name}         — display name (class name for constructors, method name otherwise)</li>
     *   <li>{@code rawName}      — proof-result lookup key: {@code "<init>"} for constructors,
     *       same as {@code name} for regular methods.  Use this to look up entries in the
     *       {@code proofResults} map returned by {@link org.openjml.lsp.CheckRunner.CheckResult}.</li>
     *   <li>{@code startLine}    — line of the method declaration (used for code-lens placement)</li>
     *   <li>{@code specStartLine} — first JML {@code //@} annotation line immediately before
     *       the declaration; equals {@code startLine} if there are no spec lines.
     *       Use this as the lower bound when matching diagnostics to a method, because
     *       OpenJML reports verification failures on the spec line, not the declaration.</li>
     *   <li>{@code endLine}      — last line attributed to this method (exclusive of next method's spec)</li>
     * </ul>
     */
    public record MethodInfo(String name, String rawName, int startLine, int specStartLine, int endLine) {
        /** Convenience: does the given 0-based line fall within this method's full range? */
        public boolean contains(int line) { return line >= specStartLine && line <= endLine; }
    }

    private static final Pattern PACKAGE_DECL = Pattern.compile(
            "^\\s*package\\s+([\\w.]+)\\s*;", Pattern.MULTILINE);

    // Line-anchored (no (?:^|\n) prefix) — used per-line in findClassName.
    private static final Pattern CLASS_DECL = Pattern.compile(
            "^[ \\t]*(?:public|protected)\\s+(?:(?:abstract|final|sealed|non-sealed)\\s+)*"
            + "(?:class|interface|enum|record)\\s+(\\w+)");

    /**
     * Extract the package name declared in {@code content}, or {@code ""} if none.
     */
    public static String findPackage(String content) {
        if (content == null) return "";
        Matcher m = PACKAGE_DECL.matcher(content);
        return m.find() ? m.group(1) : "";
    }

    /**
     * Extract the top-level public/protected class (or interface/enum/record) name
     * from {@code content}, or {@code ""} if not found.
     *
     * <p>Parses line-by-line and tracks block-comment state so that a line such as
     * {@code public class Fake} inside a {@code /* ... *}{@code /} comment or a
     * text-block literal is not mistaken for the real class declaration.
     */
    public static String findClassName(String content) {
        if (content == null) return "";
        boolean inBlockComment = false;
        for (String line : content.split("\\r?\\n", -1)) {
            String stripped = line.stripLeading();
            if (inBlockComment) {
                if (stripped.contains("*/")) inBlockComment = false;
                continue;
            }
            if (stripped.startsWith("//")) continue;
            if (stripped.startsWith("/*")) {
                if (!stripped.contains("*/")) inBlockComment = true;
                continue;
            }
            Matcher m = CLASS_DECL.matcher(line);
            if (m.find()) return m.group(1);
        }
        return "";
    }

    /**
     * Build the fully-qualified method name {@code pkg.ClassName.methodName}
     * suitable for passing to OpenJML's {@code --method} flag.
     *
     * <p>The VS Code extension replicates this logic in {@code findMethodFqnAtLine()}
     * (extension.js) for keyboard/menu invocations.  If the regex logic changes
     * here it MUST be updated there too (and vice versa).
     */
    public static String methodFqn(String content, String methodName) {
        String pkg = findPackage(content);
        String cls = findClassName(content);
        if (cls.isEmpty()) return methodName;
        if (pkg.isEmpty()) return cls + "." + methodName;
        return pkg + "." + cls + "." + methodName;
    }

    // Requires ≥1 modifier keyword to avoid matching calls and field declarations.
    // [^(;{]*[^(;{\w] consumes the return type and any other modifiers/annotations,
    // stopping at the last non-word character before the method name so that
    // (\w+) captures the full method identifier rather than just its last character.
    private static final Pattern METHOD_DECL = Pattern.compile(
            "^[ \\t]*(?:public|private|protected|static|final|synchronized|abstract|"
            + "native|default|strictfp)"
            + "[^(;{]*[^(;{\\w](\\w+)[ \\t]*\\(");

    /**
     * Return all method declarations found in {@code content}, ordered by line.
     *
     * The {@code endLine} of each entry is one line before the next method's
     * {@code startLine}, or the last line of the file for the final method.
     */
    public static List<MethodInfo> findMethods(String content) {
        if (content == null || content.isBlank()) return List.of();
        String[] lines = content.split("\\r?\\n", -1);
        List<Integer> starts = new ArrayList<>();
        List<String>  names  = new ArrayList<>();

        for (int i = 0; i < lines.length; i++) {
            String trimmed = lines[i].trim();
            // Skip comment lines and annotations — they cannot be method declarations.
            if (trimmed.startsWith("//") || trimmed.startsWith("*")
                    || trimmed.startsWith("/*") || trimmed.startsWith("@")) continue;

            Matcher m = METHOD_DECL.matcher(lines[i]);
            if (m.find()) {
                starts.add(i);
                names.add(m.group(1));
            }
        }

        List<MethodInfo> result = new ArrayList<>(starts.size());
        for (int i = 0; i < starts.size(); i++) {
            int declLine = starts.get(i);
            int end = (i + 1 < starts.size()) ? starts.get(i + 1) - 1 : lines.length - 1;
            result.add(new MethodInfo(names.get(i), names.get(i), declLine, findSpecStart(lines, declLine), end));
        }
        return result;
    }

    /**
     * Return all method declarations found by walking {@code ast}, ordered by line.
     *
     * <p>Preferred over {@link #findMethods(String)} when the AST is available: it
     * handles nested classes, constructors, and package-private methods correctly,
     * and is not fooled by commented-out code or string literals.
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
        private final String[] lines;
        final List<MethodInfo> result = new ArrayList<>();
        private int bodyDepth = 0;

        MethodLensWalker(JmlCompilationUnit cu, String[] lines) {
            super(null);   // null context → AST_JML_MODE
            this.cu    = cu;
            this.lines = lines;
        }

        @Override
        public void visitClassDef(JCClassDecl tree) {
            // Visit all classes (top-level, secondary, nested members).
            // Local and anonymous classes — which live inside a JCBlock and therefore
            // have bodyDepth > 0 — are reached here but their methods are excluded by
            // the bodyDepth guard in visitMethodDef.  They will be handled separately
            // using a character-offset key once the main refactoring is stable.
            super.visitClassDef(tree);
        }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            // bodyDepth > 0 means we are inside a method body (JCBlock); methods that
            // appear there belong to local or anonymous classes — deferred.
            if (bodyDepth > 0 || tree.pos < 0 || tree.sym == null) return;
            String rawName = tree.name != null ? tree.name.toString() : "";
            // Skip synthetic methods (<clinit> etc.); keep <init> constructors.
            if (rawName.isEmpty() || (rawName.startsWith("<") && !"<init>".equals(rawName))) return;

            // Display name: class simple name for constructors, method name otherwise.
            String ownerSimple = tree.sym.owner != null
                    ? tree.sym.owner.getSimpleName().toString() : "";
            String name = "<init>".equals(rawName)
                    ? (ownerSimple.isEmpty() ? "<init>" : ownerSimple)
                    : rawName;

            // Proof-result key: owner FQN + "." + method-with-signature.
            // Both ProofResultCollector and this walker derive the key from sym, so
            // they will always agree regardless of class nesting depth.
            String fqnKey = tree.sym.owner.toString() + "." + tree.sym.toString();

            int startLine = Math.max(0, (int) cu.lineMap.getLineNumber(tree.pos) - 1);
            int endOffset = cu.endPositions != null ? tree.getEndPosition(cu.endPositions) : -1;
            int endLine = (endOffset > tree.pos)
                    ? Math.max(startLine, (int) cu.lineMap.getLineNumber(endOffset) - 1)
                    : startLine;
            result.add(new MethodInfo(name, fqnKey, startLine, findSpecStart(lines, startLine), endLine));
        }

        @Override
        public void visitBlock(JCBlock tree) {
            bodyDepth++;
            super.visitBlock(tree);
            bodyDepth--;
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
