package org.openjml.lsp;

import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import org.eclipse.lsp4j.ParameterInformation;
import org.eclipse.lsp4j.SignatureHelp;
import org.eclipse.lsp4j.SignatureHelpParams;
import org.eclipse.lsp4j.SignatureInformation;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.util.ArrayList;
import java.util.List;

/**
 * Computes {@code textDocument/signatureHelp} responses.
 *
 * <p>Algorithm:
 * <ol>
 *   <li>Convert the LSP (line, col) cursor position to a character offset.</li>
 *   <li>Scan backward through the source to find the enclosing {@code (} of a
 *       method call, counting commas at depth 0 to determine the active parameter
 *       index.</li>
 *   <li>Walk the cached AST (if available) to find a matching {@code JCMethodDecl}
 *       and extract its parameter list for parameter labels.</li>
 *   <li>Return a {@link SignatureHelp} with one {@link SignatureInformation}
 *       entry (the first matching overload).</li>
 * </ol>
 *
 * <p>If no AST is cached yet (file not yet type-checked), the method returns an
 * empty {@link SignatureHelp} gracefully rather than throwing.
 */
public class SignatureHelpProvider {

    private SignatureHelpProvider() {}

    /**
     * Compute signature help at the cursor position.
     *
     * @param params  LSP request parameters (document URI + cursor position)
     * @param content current source text for the document
     * @param cache   the shared AST cache
     * @return a {@link SignatureHelp} (possibly empty if not in a call or no AST available)
     */
    public static SignatureHelp compute(SignatureHelpParams params,
                                        String content,
                                        ASTCache cache) {
        if (content == null) return new SignatureHelp();

        int line = params.getPosition().getLine();
        int col  = params.getPosition().getCharacter();
        int offset = DefinitionFinder.lineColToOffset(content, line, col);
        if (offset < 0) return new SignatureHelp();

        CallSite site = findCallSite(content, offset);
        if (site == null) return new SignatureHelp();

        String uri = params.getTextDocument().getUri();
        ASTCache.Entry entry = cache.get(uri);
        if (entry == null) return new SignatureHelp();

        List<JCMethodDecl> decls = findMethodDecls(entry.ast(), site.methodName());
        if (decls.isEmpty()) return new SignatureHelp();

        SignatureInformation sig = buildSignatureInfo(decls.get(0));
        SignatureHelp result = new SignatureHelp(List.of(sig), 0, site.activeParameter());
        return result;
    }

    // -----------------------------------------------------------------------
    // Call-site detection: scan backward from cursor to find enclosing '('
    // -----------------------------------------------------------------------

    private record CallSite(String methodName, int activeParameter) {}

    /**
     * Scan backward from {@code targetOffset} to find the enclosing method call.
     *
     * <p>Tracks paren/bracket depth so nested calls don't confuse the scan.
     * Stops at statement boundaries ({@code ;}, {@code {}, {@code }}).
     *
     * @return a {@link CallSite} with method name and active-parameter index, or
     *         {@code null} if the cursor is not inside a call argument list
     */
    private static CallSite findCallSite(String source, int targetOffset) {
        int i = targetOffset - 1;
        int depth = 0;
        int commas = 0;

        while (i >= 0) {
            char c = source.charAt(i);
            if (c == ')' || c == ']') {
                depth++;
            } else if (c == '(' || c == '[') {
                if (c == '[') {
                    // Array indexing — not a method call; just pop depth
                    if (depth > 0) depth--;
                    else return null;
                } else {
                    // '('
                    if (depth > 0) {
                        depth--;
                    } else {
                        // Found the enclosing '('
                        String name = extractMethodNameBefore(source, i);
                        return name != null ? new CallSite(name, commas) : null;
                    }
                }
            } else if (c == ',' && depth == 0) {
                commas++;
            } else if (c == ';' || c == '{' || c == '}') {
                // Statement boundary — not inside a call
                return null;
            }
            i--;
        }
        return null;
    }

    /**
     * Extract the method name from the source immediately before the open paren at
     * {@code openParenPos}.  Returns {@code null} if the token before {@code (} is
     * not a Java identifier or is a keyword that introduces a control-flow construct.
     */
    private static String extractMethodNameBefore(String source, int openParenPos) {
        int end = openParenPos;
        // Skip whitespace
        while (end > 0 && Character.isWhitespace(source.charAt(end - 1))) end--;
        if (end == 0) return null;
        if (!Character.isJavaIdentifierPart(source.charAt(end - 1))) return null;
        int start = end;
        while (start > 0 && Character.isJavaIdentifierPart(source.charAt(start - 1))) start--;
        String name = source.substring(start, end);
        // Skip control-flow keywords
        if (name.equals("if") || name.equals("while") || name.equals("for")
                || name.equals("switch") || name.equals("catch") || name.equals("new")
                || name.equals("return") || name.equals("throw") || name.equals("assert")) {
            return null;
        }
        return name.isEmpty() ? null : name;
    }

    // -----------------------------------------------------------------------
    // AST lookup: find JCMethodDecl nodes by simple name
    // -----------------------------------------------------------------------

    private static List<JCMethodDecl> findMethodDecls(JmlCompilationUnit ast,
                                                       String methodName) {
        MethodDeclCollector collector = new MethodDeclCollector(methodName);
        collector.scan(ast);
        return collector.found;
    }

    private static class MethodDeclCollector extends JmlTreeScanner {
        private final String target;
        final List<JCMethodDecl> found = new ArrayList<>();

        MethodDeclCollector(String target) { this.target = target; }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            if (tree.name != null && target.equals(tree.name.toString())) {
                found.add(tree);
            }
            super.visitMethodDef(tree);
        }
    }

    // -----------------------------------------------------------------------
    // Signature building
    // -----------------------------------------------------------------------

    private static SignatureInformation buildSignatureInfo(JCMethodDecl method) {
        StringBuilder label = new StringBuilder(method.name.toString()).append("(");
        List<ParameterInformation> paramInfos = new ArrayList<>();
        boolean first = true;
        for (JCVariableDecl param : method.params) {
            if (!first) label.append(", ");
            first = false;
            String typeName = param.vartype != null ? param.vartype.toString() : "?";
            String paramName = param.name != null ? param.name.toString() : "";
            String paramLabel = typeName + " " + paramName;
            label.append(paramLabel);
            paramInfos.add(new ParameterInformation(paramLabel));
        }
        label.append(")");
        if (method.restype != null) {
            label.append(" : ").append(method.restype.toString());
        }
        SignatureInformation sig = new SignatureInformation(label.toString());
        sig.setParameters(paramInfos);
        return sig;
    }
}
