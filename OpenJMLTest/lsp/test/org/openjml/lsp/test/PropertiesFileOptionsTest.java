package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Tests that OpenJML tool options are correctly transmitted to the tool
 * via a generated properties file (the {@code generatedPropertiesFile}
 * field of {@link OpenJMLSettings}).
 *
 * <p>Each test writes a small {@code .properties} file using
 * {@code org.openjml.option.<flag>=<value>} entries, sets it as
 * {@link OpenJMLSettings#generatedPropertiesFile}, and then verifies
 * that the option took effect by observing differences in the diagnostics.
 */
public class PropertiesFileOptionsTest extends LspTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Writes {@code content} to a new temp file with the given name and returns its path. */
    private String writeTempProps(String filename, String content) throws IOException {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) {
            w.write(content);
        }
        return f.getAbsolutePath();
    }

    /** Creates a fresh {@link OpenJMLSettings} with {@code generatedPropertiesFile} set. */
    private OpenJMLSettings settingsWithGeneratedFile(String path) {
        OpenJMLSettings s = new OpenJMLSettings();
        s.generatedPropertiesFile = path;
        return s;
    }

    // -----------------------------------------------------------------------
    // Test 1: --keys enables optional annotation groups
    // -----------------------------------------------------------------------

    /**
     * JML annotations guarded by an optional key ({@code //+MYKEY@ ...}) are
     * only activated when that key is listed in {@code --keys}.  This gives a
     * clean way to verify the generated properties file is applied: the same
     * source produces different ESC results depending on whether the key is
     * active.
     *
     * <p>Source layout:
     * <pre>
     * line 0: public class OptionalKey {
     * line 1:     //+MYKEY@ ensures false;   // active only when key MYKEY is enabled
     * line 2:     public int m(int x) { return x; }
     * line 3: }
     * </pre>
     *
     * Without {@code --keys=MYKEY}: the {@code ensures false} annotation is
     * ignored; the method has no spec and ESC reports nothing.
     *
     * With {@code org.openjml.option.keys=MYKEY} in the generated properties
     * file: the annotation IS active, {@code ensures false} is imposed on a
     * normally-terminating method, and ESC reports a postcondition violation.
     */
    @Test
    public void testOptionalKeyViaPropertiesFile() throws Exception {
        String source =
                "public class OptionalKey {\n" +
                "    //+MYKEY@ ensures false;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n";

        // Without the key the annotation is inactive: no ESC diagnostics.
        List<Diagnostic> defaultDiags =
                CheckRunner.runEsc("file:///OptionalKey.java", source).diagnostics();
        assertTrue("Expected no ESC diagnostics when MYKEY is not in --keys",
                defaultDiags.isEmpty());

        // With keys=MYKEY the annotation is active: ESC finds a postcondition violation.
        String propsPath = writeTempProps("optional-key.properties",
                "org.openjml.option.keys=MYKEY\n");
        OpenJMLSettings settings = settingsWithGeneratedFile(propsPath);
        List<Diagnostic> keyDiags =
                CheckRunner.runEsc("file:///OptionalKey.java", source, settings).diagnostics();
        assertFalse("Expected ESC postcondition diagnostic when MYKEY enables ensures false",
                keyDiags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Test 2: --check-feasibility=basic reports infeasible preconditions
    // -----------------------------------------------------------------------

    /**
     * A method with {@code //@ requires false;} has an infeasible precondition.
     * By default, feasibility checking is off ({@code none}), so no diagnostic
     * is produced.  With {@code org.openjml.option.check-feasibility=basic} in
     * the generated properties file, OpenJML should report the infeasibility.
     */
    @Test
    public void testFeasibilityCheckingViaPropertiesFile() throws Exception {
        String source =
                "public class FeasCheck {\n" +
                "    //@ requires false;\n" +
                "    //@ ensures \\result > 0;\n" +
                "    public int m(int x) { return x + 1; }\n" +
                "}\n";

        // Without feasibility checking there should be no diagnostics.
        List<Diagnostic> defaultDiags =
                CheckRunner.runEsc("file:///FeasCheck.java", source).diagnostics();

        // With check-feasibility=basic, a diagnostic for the infeasible precondition
        // should appear.
        String propsPath = writeTempProps("feasibility.properties",
                "org.openjml.option.check-feasibility=basic\n");
        OpenJMLSettings settings = settingsWithGeneratedFile(propsPath);
        List<Diagnostic> feasDiags =
                CheckRunner.runEsc("file:///FeasCheck.java", source, settings).diagnostics();
        assertFalse("Expected at least one diagnostic for infeasible precondition "
                + "when check-feasibility=basic",
                feasDiags.isEmpty());
        assertTrue("Expected more diagnostics with feasibility=basic than without",
                feasDiags.size() > defaultDiags.size());
    }

    // -----------------------------------------------------------------------
    // Test 3: --require-white-space (boolean option) suppresses no-space JML comments
    // -----------------------------------------------------------------------

    /**
     * Verifies that boolean options are correctly applied via the generated
     * properties file.  {@code --require-white-space} is a boolean flag: when
     * set, JML comments of the form {@code //@keyword} (no space after {@code @})
     * are treated as ordinary Java comments and their annotations are ignored.
     *
     * <p>Source layout:
     * <pre>
     * line 0: public class RequireWs {
     * line 1:     //@ensures \result > x;   // no space — JML only when flag is NOT set
     * line 2:     public int m(int x) { return x; }
     * line 3: }
     * </pre>
     *
     * Without the flag the comment is parsed as JML and ESC reports a violation.
     * With {@code org.openjml.option.require-white-space=true} in the generated
     * properties file the comment is silently ignored and ESC finds nothing.
     */
    @Test
    public void testRequireWhiteSpaceViaPropertiesFile() throws Exception {
        String source =
                "public class RequireWs {\n" +
                "    //@ensures \\result > x;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n";

        // Without the option the JML comment is parsed and ESC finds a violation.
        List<Diagnostic> defaultDiags =
                CheckRunner.runEsc("file:///RequireWs.java", source).diagnostics();
        assertFalse("Expected ESC diagnostic when //@ensures is parsed as JML",
                defaultDiags.isEmpty());

        // With require-white-space=true the comment is NOT parsed as JML,
        // so the method has no spec and ESC finds nothing.
        String propsPath = writeTempProps("require-ws.properties",
                "org.openjml.option.require-white-space=true\n");
        OpenJMLSettings settings = settingsWithGeneratedFile(propsPath);
        List<Diagnostic> noSpecDiags =
                CheckRunner.runEsc("file:///RequireWs.java", source, settings).diagnostics();
        assertTrue("Expected no ESC diagnostics when //@ensures is suppressed "
                + "by require-white-space=true",
                noSpecDiags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Test 4: user propertiesFile overrides generatedPropertiesFile
    // -----------------------------------------------------------------------

    /**
     * {@link OpenJMLSettings#propertiesFile} (the user's workspace file) is
     * appended to the command line <em>after</em> {@code generatedPropertiesFile},
     * so it takes precedence.
     *
     * <p>This test verifies the ordering with {@code --check-feasibility}:
     * <ul>
     *   <li>The generated (Eclipse) file enables feasibility checking
     *       ({@code check-feasibility=basic}), which would produce a diagnostic
     *       for {@code //@ requires false;}.</li>
     *   <li>The user's workspace file resets it to {@code none} (the default),
     *       so no feasibility diagnostic should appear.</li>
     * </ul>
     * The expected result is zero diagnostics, confirming the user file won.
     */
    @Test
    public void testUserPropertiesFileOverridesGeneratedFile() throws Exception {
        String source =
                "public class OverrideTest {\n" +
                "    //@ requires false;\n" +
                "    //@ ensures \\result > 0;\n" +
                "    public int m(int x) { return x + 1; }\n" +
                "}\n";

        // Generated file enables feasibility checking.
        String generatedPath = writeTempProps("generated.properties",
                "org.openjml.option.check-feasibility=basic\n");
        // User file disables it again (overrides the generated file).
        String userPath = writeTempProps("user.properties",
                "org.openjml.option.check-feasibility=none\n");

        OpenJMLSettings settings = settingsWithGeneratedFile(generatedPath);
        settings.propertiesFile = userPath;

        List<Diagnostic> diags =
                CheckRunner.runEsc("file:///OverrideTest.java", source, settings).diagnostics();
        assertTrue("Expected no ESC diagnostics — user file (check-feasibility=none) "
                + "should override the generated file's check-feasibility=basic",
                diags.isEmpty());
    }
}
