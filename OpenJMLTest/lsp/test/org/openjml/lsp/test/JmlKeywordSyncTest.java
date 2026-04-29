package org.openjml.lsp.test;

import org.junit.Test;
import org.openjml.lsp.JmlKeywords;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * Checks that the Eclipse UI {@code jml.tmLanguage.json} TextMate grammar file
 * is consistent with the authoritative keyword sets in {@link JmlKeywords}.
 *
 * <p>The VSCode grammar ({@code OpenJMLlsp/vscode-extension/syntaxes/jml.tmLanguage.json})
 * is intentionally empty (no coloring rules) because semantic tokens overwrite any
 * TextMate coloring after the first {@code --check}.  Only the Eclipse UI grammar
 * is checked for keyword sync.
 *
 * <p>Grammar file paths are supplied via system properties set in the Makefile:
 * <ul>
 *   <li>{@code jml.grammar.ui} — {@code OpenJMLUI/syntaxes/jml.tmLanguage.json}</li>
 * </ul>
 */
public class JmlKeywordSyncTest {

    private static final String PROP_UI = "jml.grammar.ui";

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /** Every word in {@link JmlKeywords#JML_KEYWORDS} must appear in the UI grammar,
     *  and vice versa. */
    @Test
    public void testJmlKeywordsVsGrammar() throws Exception {
        Path ui = grammarPath(PROP_UI);
        StringBuilder errors = new StringBuilder();
        checkOneGrammar("jml-keywords", JmlKeywords.JML_KEYWORDS, false, ui, errors);
        if (errors.length() > 0) fail(errors.toString());
    }

    /** Every word in {@link JmlKeywords#JML_BACKSLASH} must appear in the UI grammar,
     *  and vice versa. */
    @Test
    public void testJmlBackslashVsGrammar() throws Exception {
        Path ui = grammarPath(PROP_UI);
        StringBuilder errors = new StringBuilder();
        checkOneGrammar("jml-backslash", JmlKeywords.JML_BACKSLASH, true, ui, errors);
        if (errors.length() > 0) fail(errors.toString());
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static void checkOneGrammar(String sectionName, Set<String> javaSet,
                                         boolean stripLeadingBackslash,
                                         Path grammarFile, StringBuilder errors) throws Exception {
        Set<String> grammarSet = extractFromGrammar(grammarFile, sectionName, stripLeadingBackslash);

        TreeSet<String> inJavaNotGrammar = new TreeSet<>(javaSet);
        inJavaNotGrammar.removeAll(grammarSet);

        TreeSet<String> inGrammarNotJava = new TreeSet<>(grammarSet);
        inGrammarNotJava.removeAll(javaSet);

        if (!inJavaNotGrammar.isEmpty() || !inGrammarNotJava.isEmpty()) {
            errors.append("\nSync mismatch in ").append(grammarFile.getFileName())
                  .append(" [").append(sectionName).append("]:\n");
            if (!inJavaNotGrammar.isEmpty())
                errors.append("  In JmlKeywords but NOT in grammar: ").append(inJavaNotGrammar).append('\n');
            if (!inGrammarNotJava.isEmpty())
                errors.append("  In grammar but NOT in JmlKeywords: ").append(inGrammarNotJava).append('\n');
        }
    }

    /**
     * Extracts the set of alternation tokens from the {@code match} field of the named
     * repository section in a TextMate JSON grammar file.
     */
    private static Set<String> extractFromGrammar(Path file, String sectionName,
                                                    boolean stripLeadingBackslash) throws Exception {
        String content = Files.readString(file);

        int secIdx = content.indexOf("\"" + sectionName + "\"");
        if (secIdx < 0)
            throw new IllegalArgumentException("Section \"" + sectionName + "\" not found in " + file);

        Pattern matchPat = Pattern.compile("\"match\"\\s*:\\s*\"((?:[^\"\\\\]|\\\\.)*)\"");
        Matcher m = matchPat.matcher(content);
        if (!m.find(secIdx))
            throw new IllegalArgumentException("No \"match\" after section \"" + sectionName + "\" in " + file);

        String rawMatch = m.group(1);

        String unescaped = rawMatch
                .replace("\\\\b", "")
                .replace("\\\\(", "(")
                .replace("\\\\)", ")")
                .replace("\\\\\\\\", "\\");

        int open  = unescaped.indexOf('(');
        int close = unescaped.lastIndexOf(')');
        if (open < 0 || close <= open)
            throw new IllegalArgumentException("Cannot find alternation in match for \"" + sectionName + "\" in " + file);

        String alternation = unescaped.substring(open + 1, close);

        TreeSet<String> result = new TreeSet<>();
        for (String token : alternation.split("\\|")) {
            String t = token.trim();
            if (stripLeadingBackslash && t.startsWith("\\"))
                t = t.substring(1);
            if (!t.isEmpty()) result.add(t);
        }
        return result;
    }

    private static Path grammarPath(String propName) {
        String val = System.getProperty(propName);
        if (val == null || val.isBlank())
            throw new IllegalStateException("System property not set: " + propName
                    + "  (set -D" + propName + "=<path> in the Makefile run command)");
        return Path.of(val);
    }
}
