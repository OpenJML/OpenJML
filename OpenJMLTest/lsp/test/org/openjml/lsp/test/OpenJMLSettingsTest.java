package org.openjml.lsp.test;

import org.junit.Assume;
import org.junit.Test;
import org.openjml.lsp.ClientSettings;
import org.openjml.lsp.OpenJMLSettings;

import java.util.List;

import static org.junit.Assert.*;

/**
 * Unit tests for the boolean query methods and copy constructor of
 * {@link OpenJMLSettings}.
 *
 * <p>These methods drive the server's trigger/colorize/engine decisions;
 * they are pure string comparisons with no external dependencies.
 *
 * <p>Fields removed from {@link OpenJMLSettings} (e.g. {@code checkTriggerOn},
 * {@code toolOptions}) now live in {@link ClientSettings} and are accessed
 * via {@code settings.clientSettings.*}.
 */
public class OpenJMLSettingsTest {

    // -----------------------------------------------------------------------
    // isCheckOnEdit / isCheckOnSave / isCheckManual
    // -----------------------------------------------------------------------

    @Test
    public void testCheckOnEditDefaultIsTrue() {
        assertTrue(new OpenJMLSettings().isCheckOnEdit());
    }

    @Test
    public void testCheckOnEditSaveIsFalse() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.checkTriggerOn = "save";
        assertFalse(s.isCheckOnEdit());
    }

    @Test
    public void testCheckOnEditCaseInsensitive() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.checkTriggerOn = "SAVE";
        assertFalse(s.isCheckOnEdit());
    }

    @Test
    public void testCheckOnEditManualIsFalse() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.checkTriggerOn = "manual";
        assertFalse(s.isCheckOnEdit());
    }

    @Test
    public void testCheckOnSave() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.checkTriggerOn = "save";
        assertTrue(s.isCheckOnSave());
        assertFalse(s.isCheckOnEdit());
        assertFalse(s.isCheckManual());
    }

    @Test
    public void testCheckManual() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.checkTriggerOn = "manual";
        assertTrue(s.isCheckManual());
        assertFalse(s.isCheckOnEdit());
        assertFalse(s.isCheckOnSave());
    }

    @Test
    public void testCheckManualCaseInsensitive() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.checkTriggerOn = "MANUAL";
        assertTrue(s.isCheckManual());
    }

    // -----------------------------------------------------------------------
    // isEscOnEdit / isEscOnSave / isEscManual
    // -----------------------------------------------------------------------

    @Test
    public void testEscManualIsDefaultTrue() {
        OpenJMLSettings s = new OpenJMLSettings();
        assertFalse("isEscOnSave must be false by default", s.isEscOnSave());
        assertTrue("isEscManual must be true by default",   s.isEscManual());
    }

    @Test
    public void testEscOnSave() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.escTriggerOn = "save";
        assertTrue(s.isEscOnSave());
        assertFalse(s.isEscManual());
    }

    @Test
    public void testEscTriggerCaseInsensitive() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.escTriggerOn = "Save";
        assertTrue(s.isEscOnSave());
        s.clientSettings.escTriggerOn = "MANUAL";
        assertTrue(s.isEscManual());
    }

    // -----------------------------------------------------------------------
    // isRegexColoring — true only when syntaxColoringStrategy == "regex"
    // -----------------------------------------------------------------------

    @Test
    public void testRegexColoringDefaultFalse() {
        // Default syntaxColoringStrategy = "ast"
        assertFalse(new OpenJMLSettings().isRegexColoring());
    }

    @Test
    public void testRegexColoringWhenRegex() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.syntaxColoringStrategy = "regex";
        assertTrue(s.isRegexColoring());
    }

    @Test
    public void testRegexColoringCaseInsensitive() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.syntaxColoringStrategy = "REGEX";
        assertTrue(s.isRegexColoring());
    }

    // -----------------------------------------------------------------------
    // isEscApiMode — true only when escEngine == "concurrent"
    // -----------------------------------------------------------------------

    @Test
    public void testEscApiModeDefaultFalse() {
        // Default escEngine = "fresh"
        assertFalse(new OpenJMLSettings().isEscApiMode());
    }

    @Test
    public void testEscApiModeWhenConcurrent() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.escEngine = "concurrent";
        assertTrue(s.isEscApiMode());
    }

    @Test
    public void testEscApiModeCaseInsensitive() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.clientSettings.escEngine = "CONCURRENT";
        assertTrue(s.isEscApiMode());
    }

    // -----------------------------------------------------------------------
    // Copy constructor — assembled path fields are independent; clientSettings is shared
    // -----------------------------------------------------------------------

    @Test
    public void testCopyConstructorCopiesAssembledPaths() {
        OpenJMLSettings orig = new OpenJMLSettings();
        orig.specsPath  = "/path/to/specs";
        orig.sourcePath = "/path/to/src";
        orig.classPath  = "/path/to/classes";

        OpenJMLSettings copy = new OpenJMLSettings(orig);

        assertEquals(orig.specsPath,  copy.specsPath);
        assertEquals(orig.sourcePath, copy.sourcePath);
        assertEquals(orig.classPath,  copy.classPath);
    }

    @Test
    public void testCopyConstructorAssembledPathsAreIndependent() {
        OpenJMLSettings orig = new OpenJMLSettings();
        orig.specsPath = "/original/specs";

        OpenJMLSettings copy = new OpenJMLSettings(orig);
        copy.specsPath = "/copy/specs";

        assertEquals("orig.specsPath must not change when copy is mutated",
                "/original/specs", orig.specsPath);
        assertEquals("/copy/specs", copy.specsPath);
    }

    @Test
    public void testCopyConstructorSharesClientSettings() {
        OpenJMLSettings orig = new OpenJMLSettings();
        OpenJMLSettings copy = new OpenJMLSettings(orig);

        assertSame("Copy constructor must share clientSettings reference",
                orig.clientSettings, copy.clientSettings);
    }

    @Test
    public void testCopyConstructorCopiesToolOptions() {
        OpenJMLSettings orig = new OpenJMLSettings();
        orig.clientSettings.toolOptions = List.of("--keys", "MYKEY");
        OpenJMLSettings copy = new OpenJMLSettings(orig);
        assertEquals(orig.clientSettings.toolOptions, copy.clientSettings.toolOptions);
    }

    // -----------------------------------------------------------------------
    // expandEnvVarsInPath — path-separator-aware variant
    // -----------------------------------------------------------------------

    @Test
    public void testExpandEnvVarsInPath_null() {
        assertNull(OpenJMLSettings.expandEnvVarsInPath(null));
    }

    @Test
    public void testExpandEnvVarsInPath_blank() {
        assertEquals("   ", OpenJMLSettings.expandEnvVarsInPath("   "));
    }

    @Test
    public void testExpandEnvVarsInPath_noVars() {
        String sep = java.io.File.pathSeparator;
        assertEquals("/a" + sep + "/b", OpenJMLSettings.expandEnvVarsInPath("/a" + sep + "/b"));
    }

    @Test
    public void testExpandEnvVarsInPath_unknownStandaloneEntryRemoved() {
        // $UNKNOWN is the whole entry — it must be dropped, leaving no empty entry.
        String sep = java.io.File.pathSeparator;
        String input    = "/a" + sep + "$OPENJML_NONEXISTENT_VAR_XYZ" + sep + "/b";
        String expected = "/a" + sep + "/b";
        assertEquals("Standalone unknown-var entry must be removed",
                expected, OpenJMLSettings.expandEnvVarsInPath(input));
    }

    @Test
    public void testExpandEnvVarsInPath_unknownEmbeddedKept() {
        // $UNKNOWN embedded inside a component — component is kept (with empty string in place).
        assertEquals("/prefix//suffix",
                OpenJMLSettings.expandEnvVarsInPath("/prefix/$OPENJML_NONEXISTENT_VAR_XYZ/suffix"));
    }

    @Test
    public void testExpandEnvVarsInPath_knownVarExpanded() {
        String home = System.getenv("HOME");
        Assume.assumeNotNull(home);
        assertEquals(home + "/specs", OpenJMLSettings.expandEnvVarsInPath("$HOME/specs"));
    }

    @Test
    public void testExpandEnvVarsInPath_braceForm() {
        String home = System.getenv("HOME");
        Assume.assumeNotNull(home);
        assertEquals(home + "/specs", OpenJMLSettings.expandEnvVarsInPath("${HOME}/specs"));
    }

    @Test
    public void testExpandEnvVarsInPath_parenForm() {
        String home = System.getenv("HOME");
        Assume.assumeNotNull(home);
        assertEquals(home + "/specs", OpenJMLSettings.expandEnvVarsInPath("$(HOME)/specs"));
    }

    @Test
    public void testExpandEnvVarsInPath_unknownBraceFormRemoved() {
        String sep = java.io.File.pathSeparator;
        String result = OpenJMLSettings.expandEnvVarsInPath(
                "/a" + sep + "${OPENJML_NONEXISTENT_VAR_XYZ}" + sep + "/b");
        assertEquals("/a" + sep + "/b", result);
    }

    @Test
    public void testExpandEnvVarsInPath_unknownParenFormRemoved() {
        String sep = java.io.File.pathSeparator;
        String result = OpenJMLSettings.expandEnvVarsInPath(
                "/a" + sep + "$(OPENJML_NONEXISTENT_VAR_XYZ)" + sep + "/b");
        assertEquals("/a" + sep + "/b", result);
    }

    @Test
    public void testExpandEnvVarsInPath_noDuplicateSeparatorsForUnknown() {
        // Verify no '::' (or ';;' on Windows) survives after removing unknown standalone entry.
        String sep = java.io.File.pathSeparator;
        String result = OpenJMLSettings.expandEnvVarsInPath(
                "/a" + sep + "$OPENJML_NONEXISTENT_VAR_XYZ" + sep + "/b");
        assertFalse("Result must not contain consecutive separators",
                result.contains(sep + sep));
    }

    // -----------------------------------------------------------------------
    // expandEnvVarsInPath — single-component (no separator) cases
    // -----------------------------------------------------------------------

    @Test
    public void testExpandEnvVars_unknownVarOmitted() {
        assertEquals("", OpenJMLSettings.expandEnvVarsInPath("$OPENJML_NONEXISTENT_VAR_XYZ"));
    }

    @Test
    public void testExpandEnvVars_unknownVarOmittedMidPath() {
        assertEquals("/prefix//suffix",
                OpenJMLSettings.expandEnvVarsInPath("/prefix/$OPENJML_NONEXISTENT_VAR_XYZ/suffix"));
    }

    @Test
    public void testExpandEnvVars_unknownVarLogsWarning() {
        List<String> logs = new java.util.ArrayList<>();
        org.openjml.lsp.CheckRunner.setLogCallback(logs::add);
        try {
            OpenJMLSettings.expandEnvVarsInPath("$OPENJML_NONEXISTENT_VAR_XYZ");
        } finally {
            org.openjml.lsp.CheckRunner.setLogCallback(null);
        }
        assertTrue("Expected a log warning for unknown env var",
                logs.stream().anyMatch(l -> l.contains("OPENJML_NONEXISTENT_VAR_XYZ")));
    }

    @Test
    public void testExpandEnvVars_knownVar() {
        String path = System.getenv("PATH");
        Assume.assumeNotNull(path);
        assertEquals(path, OpenJMLSettings.expandEnvVarsInPath("$PATH"));
    }

    @Test
    public void testExpandEnvVars_knownVarEmbedded() {
        String path = System.getenv("PATH");
        Assume.assumeNotNull(path);
        assertEquals("/prefix:" + path + "/suffix",
                OpenJMLSettings.expandEnvVarsInPath("/prefix:$PATH/suffix"));
    }

    @Test
    public void testExpandEnvVars_multipleKnownVars() {
        String home = System.getenv("HOME");
        String path = System.getenv("PATH");
        Assume.assumeNotNull(home, path);
        assertEquals(home + ":" + path, OpenJMLSettings.expandEnvVarsInPath("$HOME:$PATH"));
    }

    @Test
    public void testExpandEnvVars_knownAndUnknownVar() {
        String home = System.getenv("HOME");
        Assume.assumeNotNull(home);
        // Unknown standalone entry is dropped cleanly — no trailing separator.
        assertEquals(home,
                OpenJMLSettings.expandEnvVarsInPath("$HOME:$OPENJML_NONEXISTENT_VAR_XYZ"));
    }
}
