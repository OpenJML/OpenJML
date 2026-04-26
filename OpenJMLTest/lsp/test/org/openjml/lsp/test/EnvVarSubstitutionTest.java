package org.openjml.lsp.test;

import org.junit.After;
import org.junit.Assume;
import org.junit.Test;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.OpenJMLTextDocumentService;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

/**
 * Protocol-level tests for environment-variable substitution in path settings.
 *
 * <p>These tests go through {@link OpenJMLTextDocumentService#updateProjectSettings},
 * which is the same code path taken when the Eclipse plugin or VS Code sends a
 * {@code workspace/didChangeConfiguration} message.  They verify that {@code $VARNAME}
 * tokens are expanded before the settings are stored and ultimately passed to OpenJML.
 */
public class EnvVarSubstitutionTest {

    private final List<String> logs = new ArrayList<>();

    @After
    public void clearLogCallback() {
        CheckRunner.setLogCallback(null);
        logs.clear();
    }

    private void installLogCapture() {
        CheckRunner.setLogCallback(logs::add);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static OpenJMLTextDocumentService freshService() {
        return new OpenJMLTextDocumentService(new OpenJMLSettings(), "openjml.runEsc");
    }

    private static OpenJMLSettings.ProjectConfig config(String id,
                                                         String specsPath,
                                                         String sourcePath,
                                                         String classPath) {
        OpenJMLSettings.ProjectConfig cfg = new OpenJMLSettings.ProjectConfig();
        cfg.id         = id;
        cfg.specsPath  = specsPath;
        cfg.sourcePath = sourcePath;
        cfg.classPath  = classPath;
        return cfg;
    }

    // -----------------------------------------------------------------------
    // Test (2): expansion is performed before storing — known variable
    // -----------------------------------------------------------------------

    @Test
    public void testKnownEnvVarExpandedInSpecsPath() {
        String home = System.getenv("HOME");
        Assume.assumeNotNull("$HOME must be set", home);

        OpenJMLTextDocumentService svc = freshService();
        svc.updateProjectSettings(List.of(
                config("proj", "$HOME/myspecs", "/src", "")));

        OpenJMLSettings stored = svc.getProjectSettings("proj");
        assertNotNull("Project settings must be stored after updateProjectSettings", stored);
        String sep = java.io.File.pathSeparator;
        // Server appends sourcePath to specsPath so OpenJML can find cross-file refs.
        assertEquals("specsPath must be expanded specsPath + sourcePath",
                home + "/myspecs" + sep + "/src", stored.specsPath);
        assertFalse("Stored specsPath must not contain the literal token $HOME",
                stored.specsPath.contains("$HOME"));
    }

    @Test
    public void testKnownEnvVarExpandedInClassPath() {
        String home = System.getenv("HOME");
        Assume.assumeNotNull("$HOME must be set", home);

        OpenJMLTextDocumentService svc = freshService();
        svc.updateProjectSettings(List.of(
                config("proj", null, "/src", "$HOME/lib/my.jar")));

        OpenJMLSettings stored = svc.getProjectSettings("proj");
        assertNotNull(stored);
        assertTrue("classPath must start with the expanded home directory",
                stored.classPath.startsWith(home));
        assertFalse("Stored classPath must not contain the literal token $HOME",
                stored.classPath.contains("$HOME"));
    }

    @Test
    public void testKnownEnvVarExpandedInSourcePath() {
        String home = System.getenv("HOME");
        Assume.assumeNotNull("$HOME must be set", home);

        OpenJMLTextDocumentService svc = freshService();
        svc.updateProjectSettings(List.of(
                config("proj", null, "$HOME/src", "")));

        OpenJMLSettings stored = svc.getProjectSettings("proj");
        assertNotNull(stored);
        assertTrue("sourcePath must start with the expanded home directory",
                stored.sourcePath.startsWith(home));
        assertFalse("Stored sourcePath must not contain the literal token $HOME",
                stored.sourcePath.contains("$HOME"));
    }

    // -----------------------------------------------------------------------
    // Test (3): malformed / non-existent path after expansion — must not crash
    // -----------------------------------------------------------------------

    @Test
    public void testNonExistentPathAfterExpansionDoesNotCrash() {
        String home = System.getenv("HOME");
        Assume.assumeNotNull("$HOME must be set", home);

        // After expansion this is a syntactically valid but non-existent path.
        OpenJMLTextDocumentService svc = freshService();
        svc.updateProjectSettings(List.of(
                config("proj", "$HOME/nonexistent_jml_specs_xyzzy_abc", "/src", "")));

        OpenJMLSettings stored = svc.getProjectSettings("proj");
        assertNotNull(stored);
        // Expanded to a real path — system must not crash on storing it.
        // Server appends sourcePath to specsPath.
        String sep = java.io.File.pathSeparator;
        assertEquals(home + "/nonexistent_jml_specs_xyzzy_abc" + sep + "/src", stored.specsPath);
    }

    @Test
    public void testUnknownEnvVarOmittedAndLogged() {
        installLogCapture();

        // $UNKNOWN is a standalone path entry — it must be dropped with no :: residue.
        String sep = java.io.File.pathSeparator;
        String input = "/a" + sep + "$OPENJML_NONEXISTENT_VAR_XYZ" + sep + "/b";
        OpenJMLTextDocumentService svc = freshService();
        svc.updateProjectSettings(List.of(config("proj", null, input, "")));

        OpenJMLSettings stored = svc.getProjectSettings("proj");
        assertNotNull(stored);
        assertFalse("sourcePath must not contain the literal unknown token",
                stored.sourcePath.contains("$OPENJML_NONEXISTENT_VAR_XYZ"));
        assertFalse("sourcePath must not contain consecutive separators (:: / ;;)",
                stored.sourcePath.contains(sep + sep));
        assertEquals("sourcePath must equal /a" + sep + "/b",
                "/a" + sep + "/b", stored.sourcePath);

        assertTrue("A warning must be logged for the unknown environment variable",
                logs.stream().anyMatch(l -> l.contains("OPENJML_NONEXISTENT_VAR_XYZ")));
    }
}
