package org.openjml.lsp;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Scans Java source text to locate method (and constructor) declarations.
 *
 * Uses a regex heuristic that requires at least one explicit access or modifier
 * keyword ({@code public}, {@code private}, {@code protected}, {@code static},
 * etc.).  This intentionally excludes package-private declarations to keep
 * false-positive rates low — method calls and local-variable declarations are
 * the most common source of ambiguity and they never carry modifier keywords.
 *
 * Results are approximate and suitable for code-lens placement; they are not
 * a substitute for a full parse.
 */
public class JavaSourceScanner {

    /**
     * Immutable description of one method found in a source file.
     *
     * <ul>
     *   <li>{@code startLine}    — line of the method declaration (used for code-lens placement)</li>
     *   <li>{@code specStartLine} — first JML {@code //@} annotation line immediately before
     *       the declaration; equals {@code startLine} if there are no spec lines.
     *       Use this as the lower bound when matching diagnostics to a method, because
     *       OpenJML reports verification failures on the spec line, not the declaration.</li>
     *   <li>{@code endLine}      — last line attributed to this method (exclusive of next method's spec)</li>
     * </ul>
     */
    public record MethodInfo(String name, int startLine, int specStartLine, int endLine) {
        /** Convenience: does the given 0-based line fall within this method's full range? */
        public boolean contains(int line) { return line >= specStartLine && line <= endLine; }
    }

    private static final Pattern PACKAGE_DECL = Pattern.compile(
            "^\\s*package\\s+([\\w.]+)\\s*;", Pattern.MULTILINE);

    private static final Pattern CLASS_DECL = Pattern.compile(
            "(?:^|\\n)[ \\t]*(?:public|protected)\\s+(?:(?:abstract|final|sealed|non-sealed)\\s+)*"
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
     */
    public static String findClassName(String content) {
        if (content == null) return "";
        Matcher m = CLASS_DECL.matcher(content);
        return m.find() ? m.group(1) : "";
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
    // Uses a reluctant .*? so the first "word(" after the modifiers is captured
    // as the method/constructor name rather than something inside the parameter list.
    private static final Pattern METHOD_DECL = Pattern.compile(
            "^[ \\t]*(?:public|private|protected|static|final|synchronized|abstract|"
            + "native|default|strictfp)"
            + ".*?(\\w+)[ \\t]*\\(");

    /**
     * Return all method declarations found in {@code content}, ordered by line.
     *
     * The {@code endLine} of each entry is one line before the next method's
     * {@code startLine}, or the last line of the file for the final method.
     */
    public static List<MethodInfo> findMethods(String content) {
        if (content == null || content.isBlank()) return List.of();
        String[] lines = content.split("\n", -1);
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
            // Walk backwards to find the first consecutive JML spec line before the declaration.
            int specStart = declLine;
            for (int j = declLine - 1; j >= 0; j--) {
                String t = lines[j].trim();
                if (t.startsWith("//@")) specStart = j;
                else if (t.isEmpty() || t.startsWith("//") || t.startsWith("*")
                        || t.startsWith("/*") || t.startsWith("@")) { /* skip */ }
                else break;
            }
            result.add(new MethodInfo(names.get(i), declLine, specStart, end));
        }
        return result;
    }
}
