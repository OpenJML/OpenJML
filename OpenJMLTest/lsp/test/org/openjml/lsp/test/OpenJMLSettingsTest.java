package org.openjml.lsp.test;

import org.junit.Test;
import org.openjml.lsp.OpenJMLSettings;

import java.util.List;

import static org.junit.Assert.*;

/**
 * Unit tests for the boolean query methods and copy constructor of
 * {@link OpenJMLSettings}.
 *
 * <p>These methods drive the server's trigger/colorize/engine decisions;
 * they are pure string comparisons with no external dependencies.
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
        s.checkTriggerOn = "save";
        assertFalse(s.isCheckOnEdit());
    }

    @Test
    public void testCheckOnEditCaseInsensitive() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.checkTriggerOn = "SAVE";
        assertFalse(s.isCheckOnEdit());
    }

    @Test
    public void testCheckOnEditManualIsFalse() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.checkTriggerOn = "manual";
        assertFalse(s.isCheckOnEdit());
    }

    @Test
    public void testCheckOnSave() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.checkTriggerOn = "save";
        assertTrue(s.isCheckOnSave());
        assertFalse(s.isCheckOnEdit());
        assertFalse(s.isCheckManual());
    }

    @Test
    public void testCheckManual() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.checkTriggerOn = "manual";
        assertTrue(s.isCheckManual());
        assertFalse(s.isCheckOnEdit());
        assertFalse(s.isCheckOnSave());
    }

    @Test
    public void testCheckManualCaseInsensitive() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.checkTriggerOn = "MANUAL";
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
        s.escTriggerOn = "save";
        assertTrue(s.isEscOnSave());
        assertFalse(s.isEscManual());
    }

    @Test
    public void testEscTriggerCaseInsensitive() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.escTriggerOn = "Save";
        assertTrue(s.isEscOnSave());
        s.escTriggerOn = "MANUAL";
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
        s.syntaxColoringStrategy = "regex";
        assertTrue(s.isRegexColoring());
    }

    @Test
    public void testRegexColoringCaseInsensitive() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.syntaxColoringStrategy = "REGEX";
        assertTrue(s.isRegexColoring());
    }

    // -----------------------------------------------------------------------
    // isEscApiMode — true only when escEngine == "concurrent"
    // -----------------------------------------------------------------------

    @Test
    public void testEscApiModeDefaultFalse() {
        // Default escEngine = "subprocess"
        assertFalse(new OpenJMLSettings().isEscApiMode());
    }

    @Test
    public void testEscApiModeWhenConcurrent() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.escEngine = "concurrent";
        assertTrue(s.isEscApiMode());
    }

    @Test
    public void testEscApiModeCaseInsensitive() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.escEngine = "CONCURRENT";
        assertTrue(s.isEscApiMode());
    }

    // -----------------------------------------------------------------------
    // Copy constructor — fields are copied; mutation is independent
    // -----------------------------------------------------------------------

    @Test
    public void testCopyConstructorCopiesFields() {
        OpenJMLSettings orig = new OpenJMLSettings();
        orig.checkTriggerOn         = "save";
        orig.escTriggerOn           = "save";
        orig.syntaxColoringStrategy = "regex";
        orig.escEngine              = "concurrent";
        orig.specsPath              = "/path/to/specs";

        OpenJMLSettings copy = new OpenJMLSettings(orig);

        assertEquals(orig.checkTriggerOn,         copy.checkTriggerOn);
        assertEquals(orig.escTriggerOn,           copy.escTriggerOn);
        assertEquals(orig.syntaxColoringStrategy, copy.syntaxColoringStrategy);
        assertEquals(orig.escEngine,              copy.escEngine);
        assertEquals(orig.specsPath,              copy.specsPath);
    }

    @Test
    public void testCopyConstructorCopiesToolOptions() {
        OpenJMLSettings orig = new OpenJMLSettings();
        orig.toolOptions = List.of("--keys", "MYKEY");
        OpenJMLSettings copy = new OpenJMLSettings(orig);
        assertEquals(orig.toolOptions, copy.toolOptions);
    }

    @Test
    public void testCopyConstructorToolOptionsIsIndependent() {
        OpenJMLSettings orig = new OpenJMLSettings();
        orig.toolOptions = List.of("--keys", "A");
        OpenJMLSettings copy = new OpenJMLSettings(orig);
        copy.toolOptions = List.of("--keys", "B");
        assertEquals("orig.toolOptions must not change when copy is mutated",
                List.of("--keys", "A"), orig.toolOptions);
    }

    @Test
    public void testCopyConstructorIsIndependent() {
        OpenJMLSettings orig = new OpenJMLSettings();
        orig.checkTriggerOn = "edit";
        OpenJMLSettings copy = new OpenJMLSettings(orig);

        copy.checkTriggerOn = "save";
        // Mutation of copy must not affect original
        assertTrue("orig.isCheckOnEdit() must remain true after mutating copy",
                orig.isCheckOnEdit());
        assertFalse("copy.isCheckOnEdit() must be false after mutation",
                copy.isCheckOnEdit());
    }
}
