package org.openjml.lsp.test;

import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import java.io.File;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * Verifies that {@link AllLspTests} {@code @Suite.SuiteClasses} and the Makefile
 * {@code TEST_CLASSES} list are in sync — every class in one must appear in the other.
 *
 * <p>Requires the {@code lsp.testdata} system property (set by the Makefile when
 * running under {@code make run-tests}).  The test is skipped gracefully when the
 * property is absent (e.g. IDE run without the property).
 */
public class SuiteVsMakefileTest {

    @Test
    public void testSuiteClassesMatchMakefileTestClasses() throws Exception {
        // Derive the Makefile path from the lsp.testdata property.
        String testdataProp = System.getProperty("lsp.testdata");
        Assume.assumeTrue("lsp.testdata not set; skipping Makefile sync check",
                testdataProp != null);
        File makefile = new File(new File(testdataProp).getParentFile(), "Makefile");
        Assume.assumeTrue("Makefile not found at " + makefile + "; skipping sync check",
                makefile.isFile());

        // Parse TEST_CLASSES from the Makefile.
        String content = Files.readString(makefile.toPath());
        Set<String> makefileClasses = parseMakefileTestClasses(content);
        assertFalse("No TEST_CLASSES entries found in Makefile", makefileClasses.isEmpty());

        // Extract simple class names from @Suite.SuiteClasses on AllLspTests.
        Suite.SuiteClasses annotation = AllLspTests.class.getAnnotation(Suite.SuiteClasses.class);
        assertNotNull("AllLspTests is missing @Suite.SuiteClasses annotation", annotation);
        Set<String> suiteClasses = Arrays.stream(annotation.value())
                .map(Class::getSimpleName)
                .collect(Collectors.toCollection(TreeSet::new));

        Set<String> onlyInMakefile = new TreeSet<>(makefileClasses);
        onlyInMakefile.removeAll(suiteClasses);
        Set<String> onlyInSuite = new TreeSet<>(suiteClasses);
        onlyInSuite.removeAll(makefileClasses);

        assertTrue(
                "TEST_CLASSES / @Suite.SuiteClasses mismatch:\n" +
                "  In Makefile only: " + onlyInMakefile + "\n" +
                "  In AllLspTests only: " + onlyInSuite,
                onlyInMakefile.isEmpty() && onlyInSuite.isEmpty());
    }

    /**
     * Extract the set of names from the {@code TEST_CLASSES := \ ... } block in the
     * Makefile.  Each continuation line (ending with {@code \}) contributes one name;
     * the final line (no trailing {@code \}) contributes the last name.
     */
    private static Set<String> parseMakefileTestClasses(String content) {
        Pattern start = Pattern.compile("^TEST_CLASSES\\s*:=", Pattern.MULTILINE);
        Matcher m = start.matcher(content);
        if (!m.find()) return Set.of();

        Set<String> result = new TreeSet<>();
        for (String line : content.substring(m.end()).split("\n")) {
            String trimmed = line.strip();
            boolean continues = trimmed.endsWith("\\");
            String token = continues ? trimmed.substring(0, trimmed.length() - 1).strip() : trimmed;
            if (!token.isEmpty()) result.add(token);
            if (!continues) break;
        }
        return result;
    }
}
