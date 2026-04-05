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
 * Checks that the two {@code jml.tmLanguage.json} TextMate grammar files are consistent
 * with the authoritative keyword sets in {@link JmlKeywords}.
 *
 * <p>Grammar file paths are supplied via system properties set in the Makefile:
 * <ul>
 *   <li>{@code jml.grammar.lsp} — {@code OpenJMLlsp/vscode-extension/syntaxes/jml.tmLanguage.json}</li>
 *   <li>{@code jml.grammar.ui}  — {@code OpenJMLUI/syntaxes/jml.tmLanguage.json}</li>
 * </ul>
 */
public class JmlKeywordSyncTest {

    private static final String PROP_LSP = "jml.grammar.lsp";
    private static final String PROP_UI  = "jml.grammar.ui";

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /** Every word in {@link JmlKeywords#JML_KEYWORDS} must appear in both grammar files,
     *  and vice versa. */
    @Test
    public void testJmlKeywordsVsGrammar() throws Exception {
        checkSync("jml-keywords", JmlKeywords.JML_KEYWORDS, false);
    }

    /** Every word in {@link JmlKeywords#JML_BACKSLASH} must appear in both grammar files,
     *  and vice versa. */
    @Test
    public void testJmlBackslashVsGrammar() throws Exception {
        checkSync("jml-backslash", JmlKeywords.JML_BACKSLASH, true);
    }

    /** The LSP and UI grammar files must be identical. */
    @Test
    public void testGrammarsIdentical() throws Exception {
        Path lsp = grammarPath(PROP_LSP);
        Path ui  = grammarPath(PROP_UI);
        String lspContent = Files.readString(lsp);
        String uiContent  = Files.readString(ui);
        assertEquals("Grammar files differ:\n  " + lsp + "\n  " + ui, lspContent, uiContent);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Core sync check.
     * @param sectionName  the JSON repository key ({@code "jml-keywords"} or {@code "jml-backslash"})
     * @param javaSet      the authoritative set from {@link JmlKeywords}
     * @param stripLeadingBackslash if true, the grammar match has a literal {@code \} before the
     *                     alternation (backslash expressions), which must be stripped from extracted tokens
     */
    private static void checkSync(String sectionName, Set<String> javaSet,
                                   boolean stripLeadingBackslash) throws Exception {
        Path lsp = grammarPath(PROP_LSP);
        Path ui  = grammarPath(PROP_UI);

        StringBuilder errors = new StringBuilder();
        checkOneGrammar(sectionName, javaSet, stripLeadingBackslash, lsp, errors);
        checkOneGrammar(sectionName, javaSet, stripLeadingBackslash, ui,  errors);

        if (errors.length() > 0) fail(errors.toString());
    }

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
     *
     * <p>The match patterns look like (after JSON-unescaping):
     * <ul>
     *   <li>jml-keywords: {@code \b(word1|word2|...)\b}</li>
     *   <li>jml-backslash: {@code \\(word1|word2|...)\b}</li>
     * </ul>
     */
    private static Set<String> extractFromGrammar(Path file, String sectionName,
                                                    boolean stripLeadingBackslash) throws Exception {
        String content = Files.readString(file);

        // Find the named section, then the "match" field within it.
        int secIdx = content.indexOf("\"" + sectionName + "\"");
        if (secIdx < 0)
            throw new IllegalArgumentException("Section \"" + sectionName + "\" not found in " + file);

        // The match value is a JSON string: extract the raw value between the quotes.
        Pattern matchPat = Pattern.compile("\"match\"\\s*:\\s*\"((?:[^\"\\\\]|\\\\.)*)\"");
        Matcher m = matchPat.matcher(content);
        if (!m.find(secIdx))
            throw new IllegalArgumentException("No \"match\" after section \"" + sectionName + "\" in " + file);

        String rawMatch = m.group(1);

        // Unescape the JSON string value: \\ → \, \b → (removed — word boundary), \( → (
        // We don't need full JSON unescaping; just enough to extract the alternation.
        String unescaped = rawMatch
                .replace("\\\\b", "")     // \b word-boundary markers
                .replace("\\\\(", "(")    // escaped open paren
                .replace("\\\\)", ")")    // escaped close paren
                .replace("\\\\\\\\", "\\"); // \\ → \

        // Extract the alternation: between the first '(' and last ')'.
        int open  = unescaped.indexOf('(');
        int close = unescaped.lastIndexOf(')');
        if (open < 0 || close <= open)
            throw new IllegalArgumentException("Cannot find alternation in match for \"" + sectionName + "\" in " + file);

        String alternation = unescaped.substring(open + 1, close);

        TreeSet<String> result = new TreeSet<>();
        for (String token : alternation.split("\\|")) {
            String t = token.trim();
            // For backslash sections the literal \ precedes the alternation;
            // after our unescaping it shows up as a leading \ on the first token only.
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
