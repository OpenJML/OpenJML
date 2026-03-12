package org.openjml.lsp;

import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import org.eclipse.lsp4j.ParameterInformation;
import org.eclipse.lsp4j.SignatureHelp;
import org.eclipse.lsp4j.SignatureInformation;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.util.ArrayList;
import java.util.List;

/**
 * Provides {@code textDocument/signatureHelp} — parameter hints for the
 * method call or constructor at the cursor position.
 *
 * <p>Algorithm:
 * <ol>
 *   <li>Convert (line, col) to a character offset in the source.</li>
 *   <li>Scan backwards to find the innermost unclosed {@code (}, counting
 *       top-level commas to determine the active parameter index.</li>
 *   <li>Extract the identifier immediately before the {@code (} as the
 *       method/constructor name.</li>
 *   <li>Walk the attributed AST for all {@code JCMethodDecl} nodes with that
 *       name (including constructors matched by enclosing class name).</li>
 *   <li>Build {@link SignatureInformation} for each overload and pick the
 *       best match based on parameter count.</li>
 * </ol>
 *
 * <p>Works for Java method calls and constructors that appear in both Java
 * code and JML clauses ({@code //@ requires}, {@code //@ ensures}, etc.),
 * provided the AST has been attributed by a prior {@code --check} run.
 */
public class SignatureHelpProvider {

    private SignatureHelpProvider() {}

    // -----------------------------------------------------------------------
    // Public API
    // -----------------------------------------------------------------------

    /**
     * Compute signature help for the call site at ({@code line}, {@code col}).
     *
     * @param content document text
     * @param line    0-indexed line number
     * @param col     0-indexed column number
     * @param entry   attributed AST cache entry (may be {@code null})
     * @return {@link SignatureHelp}, or {@code null} if not in a call context
     *         or no matching methods are found
     */
    public static SignatureHelp compute(
            String content, int line, int col, ASTCache.Entry entry) {

        int offset = DefinitionFinder.lineColToOffset(content, line, col);
        CallSite site = findCallSite(content, offset);
        if (site == null || site.methodName().isEmpty()) return null;

        List<JCMethodDecl> methods = entry != null
                ? collectMethods(entry, site.methodName())
                : List.of();
        if (methods.isEmpty()) return null;

        List<SignatureInformation> sigs = new ArrayList<>();
        int bestSig = 0;
        int bestDiff = Integer.MAX_VALUE;

        for (int i = 0; i < methods.size(); i++) {
            JCMethodDecl m = methods.get(i);
            sigs.add(buildSignatureInfo(m));
            // Pick the overload whose parameter count is closest to the active index + 1.
            int diff = Math.abs(m.params.size() - (site.activeParam() + 1));
            if (diff < bestDiff) { bestDiff = diff; bestSig = i; }
        }

        return new SignatureHelp(sigs, bestSig, site.activeParam());
    }

    // -----------------------------------------------------------------------
    // Call site detection
    // -----------------------------------------------------------------------

    /** A call site: the callee name and which parameter (0-based) is active. */
    public record CallSite(String methodName, int activeParam) {}

    /**
     * Scan backwards from {@code offset} to find the innermost unclosed
     * {@code (}.  Returns the method name before it and the number of
     * top-level commas between {@code (} and {@code offset} (= active parameter
     * index), or {@code null} if not in a call context.
     */
    public static CallSite findCallSite(String content, int offset) {
        int depth = 0;
        for (int i = offset - 1; i >= 0; i--) {
            char c = content.charAt(i);
            if (c == ')' || c == ']' || c == '}') {
                depth++;
            } else if ((c == '[' || c == '{') && depth > 0) {
                depth--;
            } else if (c == '(') {
                if (depth > 0) {
                    depth--;
                } else {
                    String name = methodNameBefore(content, i);
                    if (name == null || name.isEmpty()) return null;
                    int activeParam = countTopLevelCommas(content, i + 1, offset);
                    return new CallSite(name, activeParam);
                }
            }
        }
        return null;
    }

    /** Count top-level commas (not inside nested brackets) in {@code content[start..end)}. */
    public static int countTopLevelCommas(String content, int start, int end) {
        int count = 0, depth = 0;
        for (int i = start; i < Math.min(end, content.length()); i++) {
            char c = content.charAt(i);
            if (c == '(' || c == '[' || c == '{') depth++;
            else if (c == ')' || c == ']' || c == '}') depth--;
            else if (c == ',' && depth == 0) count++;
        }
        return count;
    }

    /** Extract the Java identifier immediately before the {@code (} at {@code parenPos}. */
    public static String methodNameBefore(String content, int parenPos) {
        int i = parenPos - 1;
        while (i >= 0 && Character.isWhitespace(content.charAt(i))) i--;
        int end = i + 1;
        while (i >= 0 && (Character.isLetterOrDigit(content.charAt(i))
                          || content.charAt(i) == '_')) i--;
        return (i + 1 < end) ? content.substring(i + 1, end) : "";
    }

    // -----------------------------------------------------------------------
    // AST scanning
    // -----------------------------------------------------------------------

    private static List<JCMethodDecl> collectMethods(ASTCache.Entry entry, String name) {
        MethodCollector collector = new MethodCollector(name);
        collector.scan(entry.ast());
        return collector.methods;
    }

    private static class MethodCollector extends JmlTreeScanner {
        private final String name;
        final List<JCMethodDecl> methods = new ArrayList<>();

        MethodCollector(String n) { this.name = n; }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            String mname = tree.name.toString();
            if (mname.equals(name)) {
                methods.add(tree);
            } else if ("<init>".equals(mname)
                       && tree.sym != null && tree.sym.owner != null
                       && tree.sym.owner.name.toString().equals(name)) {
                // Constructor matched by enclosing class name.
                methods.add(tree);
            }
            super.visitMethodDef(tree);
        }
    }

    // -----------------------------------------------------------------------
    // Signature building
    // -----------------------------------------------------------------------

    private static SignatureInformation buildSignatureInfo(JCMethodDecl m) {
        boolean isCtor = "<init>".equals(m.name.toString());
        StringBuilder label = new StringBuilder();

        if (!isCtor) {
            if (m.restype != null) {
                label.append(shortType(m.restype.toString())).append(" ");
            }
            label.append(m.name.toString());
        } else {
            // Use the enclosing class name for constructors.
            String owner = (m.sym != null && m.sym.owner != null)
                    ? m.sym.owner.name.toString() : "";
            label.append(owner);
        }

        label.append("(");
        List<ParameterInformation> params = new ArrayList<>();
        boolean first = true;
        for (JCVariableDecl p : m.params) {
            if (!first) label.append(", ");
            first = false;
            String typeName = shortType(p.vartype != null ? p.vartype.toString()
                    : p.sym != null && p.sym.type != null ? p.sym.type.toString() : "?");
            String pLabel = typeName + " " + p.name.toString();
            label.append(pLabel);
            params.add(new ParameterInformation(pLabel));
        }
        label.append(")");

        SignatureInformation si = new SignatureInformation(label.toString());
        si.setParameters(params);
        return si;
    }

    /**
     * Strip Java package prefixes from a type string.
     * For example: {@code java.lang.String} → {@code String},
     * {@code java.util.List<java.lang.Integer>} → {@code List<Integer>}.
     */
    public static String shortType(String t) {
        // Replace sequences of lowercase-package-segments followed by a capitalized name.
        return t.replaceAll("(?:[a-z][a-zA-Z0-9_]*\\.)+([A-Za-z][a-zA-Z0-9_$]*)", "$1");
    }
}
