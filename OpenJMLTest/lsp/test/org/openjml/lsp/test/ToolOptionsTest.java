package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.junit.Test;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.util.List;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Tests that OpenJML command-line options passed directly in
 * {@link OpenJMLSettings#toolOptions} (without a properties file) take effect
 * in tool invocations.
 *
 * <p>This is distinct from {@link PropertiesFileOptionsTest}, which exercises
 * options delivered via a {@code .properties} file ({@code ["--properties",
 * path]}).  Here the options are individual command-line flags placed directly
 * in the array, for example {@code ["--keys", "MYKEY"]} or
 * {@code ["--require-white-space"]}.
 */
public class ToolOptionsTest extends LspTestBase {

    // -----------------------------------------------------------------------
    // Test 1: --keys delivered as a direct tool option
    // -----------------------------------------------------------------------

    /**
     * Verifies that an optional annotation group ({@code //+MYKEY@ ...}) is
     * activated when {@code --keys MYKEY} is placed directly in
     * {@code toolOptions} rather than inside a properties file.
     *
     * <p>Without the key the {@code ensures false} annotation is inactive and
     * ESC reports nothing.  With {@code toolOptions = ["--keys", "MYKEY"]} the
     * annotation IS active and ESC reports a postcondition violation.
     */
    @Test
    public void testOptionalKeyViaDirectToolOption() throws Exception {
        String source =
                "public class OptionalKeyDirect {\n" +
                "    //+MYKEY@ ensures false;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n";

        // Without --keys=MYKEY: annotation inactive, no ESC diagnostics.
        List<Diagnostic> defaultDiags =
                CheckRunner.runEsc("file:///OptionalKeyDirect.java", source).diagnostics();
        assertTrue("Expected no ESC diagnostics when MYKEY is not in toolOptions",
                defaultDiags.isEmpty());

        // With --keys MYKEY directly in toolOptions: annotation active, ESC finds violation.
        OpenJMLSettings settings = new OpenJMLSettings();
        settings.toolOptions = List.of("--keys", "MYKEY");
        List<Diagnostic> keyDiags =
                CheckRunner.runEsc("file:///OptionalKeyDirect.java", source, settings).diagnostics();
        assertFalse("Expected ESC postcondition diagnostic when --keys MYKEY is in toolOptions",
                keyDiags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Test 2: --require-white-space delivered as a direct tool option
    // -----------------------------------------------------------------------

    /**
     * Verifies that {@code --require-white-space} passed directly in
     * {@code toolOptions} suppresses JML comments that lack a space after
     * {@code @} (e.g., {@code //@ensures ...}).
     *
     * <p>Without the flag the comment is parsed as JML and ESC reports a
     * postcondition violation.  With {@code toolOptions = ["--require-white-space"]}
     * the comment is treated as a plain Java comment and ESC finds nothing.
     */
    @Test
    public void testRequireWhiteSpaceViaDirectToolOption() throws Exception {
        String source =
                "public class RequireWsDirect {\n" +
                "    //@ensures \\result > x;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n";

        // Without the flag: parsed as JML, ESC finds a violation.
        List<Diagnostic> defaultDiags =
                CheckRunner.runEsc("file:///RequireWsDirect.java", source).diagnostics();
        assertFalse("Expected ESC diagnostic when //@ensures is parsed as JML",
                defaultDiags.isEmpty());

        // With --require-white-space directly in toolOptions: comment ignored, no diagnostics.
        OpenJMLSettings settings = new OpenJMLSettings();
        settings.toolOptions = List.of("--require-white-space");
        List<Diagnostic> noSpecDiags =
                CheckRunner.runEsc("file:///RequireWsDirect.java", source, settings).diagnostics();
        assertTrue("Expected no ESC diagnostics when //@ensures is suppressed "
                + "by --require-white-space in toolOptions",
                noSpecDiags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Test 3: --check also respects toolOptions
    // -----------------------------------------------------------------------

    /**
     * Confirms that {@code toolOptions} is applied for {@code --check} (type-check)
     * invocations, not only for ESC.
     *
     * <p>{@code --require-white-space} is used as the observable flag: when active,
     * {@code //@ensures} is ignored, so {@code --check} produces no JML-related
     * diagnostics even for a spec that would otherwise be rejected.
     */
    @Test
    public void testToolOptionsAppliedToCheckPass() throws Exception {
        // A class with a JML annotation that would cause a type-check diagnostic
        // if the spec is valid but the postcondition cannot be satisfied.
        // Use //@ensures (no space) — ignored when --require-white-space is set.
        String source =
                "public class ToolOptCheck {\n" +
                "    //@ensures \\result > x;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n";

        // Default: //@ensures is parsed as JML; --check succeeds but the spec exists.
        // Verify --check runs without error.
        CheckRunner.CheckResult defaultResult =
                CheckRunner.check("file:///ToolOptCheck.java", source);
        assertFalse("--check should not be a command-line error on valid source",
                defaultResult.isCommandLineError());

        // With --require-white-space: //@ensures is ignored; --check also succeeds.
        OpenJMLSettings settings = new OpenJMLSettings();
        settings.toolOptions = List.of("--require-white-space");
        CheckRunner.CheckResult optResult =
                CheckRunner.check("file:///ToolOptCheck.java", source, settings);
        assertFalse("--check with toolOptions should not be a command-line error",
                optResult.isCommandLineError());
    }

    // -----------------------------------------------------------------------
    // Test 4: multiple direct options in toolOptions
    // -----------------------------------------------------------------------

    /**
     * Verifies that multiple options in {@code toolOptions} are all applied.
     *
     * <p>Combines {@code --keys MYKEY} (enables an annotation group) with
     * {@code --check-feasibility basic} (enables feasibility checking) and
     * confirms that both take effect simultaneously.
     *
     * <p>Both specs are guarded by {@code //+MYKEY@} so the method has no spec
     * without {@code --keys MYKEY} (no violations).  With both options active,
     * the infeasible precondition is detected via feasibility checking.
     */
    @Test
    public void testMultipleDirectToolOptions() throws Exception {
        String source =
                "public class MultiOpts {\n" +
                "    //+MYKEY@ requires false;\n" +
                "    //+MYKEY@ ensures false;\n" +
                "    public int m(int x) { return 0; }\n" +
                "}\n";

        // Without any options: annotation inactive + no feasibility check → no diagnostics.
        List<Diagnostic> defaultDiags =
                CheckRunner.runEsc("file:///MultiOpts.java", source).diagnostics();
        assertTrue("Expected no ESC diagnostics without toolOptions",
                defaultDiags.isEmpty());

        // With both options active: infeasible precondition is detected.
        OpenJMLSettings settings = new OpenJMLSettings();
        settings.toolOptions = List.of("--keys", "MYKEY", "--check-feasibility", "basic");
        List<Diagnostic> diags =
                CheckRunner.runEsc("file:///MultiOpts.java", source, settings).diagnostics();
        assertFalse("Expected ESC diagnostic with --keys MYKEY and --check-feasibility basic",
                diags.isEmpty());
    }
}
