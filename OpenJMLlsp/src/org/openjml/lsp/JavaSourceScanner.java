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

    /** Immutable description of one method found in a source file. */
    public record MethodInfo(String name, int startLine, int endLine) {}

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
            int end = (i + 1 < starts.size()) ? starts.get(i + 1) - 1 : lines.length - 1;
            result.add(new MethodInfo(names.get(i), starts.get(i), end));
        }
        return result;
    }
}
