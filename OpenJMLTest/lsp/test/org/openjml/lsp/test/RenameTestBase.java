package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.TextEdit;
import org.eclipse.lsp4j.WorkspaceEdit;
import org.junit.Before;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.DefinitionFinder;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.Renamer;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Shared infrastructure for {@link RenameTest1}, {@link RenameTest2}, {@link RenameTest3}.
 *
 * <p>Test data: {@code OpenJMLTest/lsp/testdata/testGoToDefinition/} (shared
 * with {@link DefinitionFinderTest}).
 *
 * <p>Each test uses a DIFFERENT-LENGTH new name to make it easy to detect
 * that the rename actually changed text rather than leaving the old name in place.
 */
public abstract class RenameTestBase extends LspTestBase {

    protected Path testdir;
    protected String primaryUri, helperUri;
    protected String primarySrc, helperSrc;
    protected OpenJMLSettings settings;

    @Before
    public void setUp() throws Exception {
        String root = System.getProperty("lsp.testdata");
        assertNotNull("System property lsp.testdata must be set", root);
        testdir = Path.of(root, "testGoToDefinition");
        assertTrue("testGoToDefinition directory must exist", testdir.toFile().isDirectory());

        primarySrc = Files.readString(testdir.resolve("Primary.java"));
        helperSrc  = Files.readString(testdir.resolve("Helper.java"));
        primaryUri = testdir.resolve("Primary.java").toUri().toString();
        helperUri  = testdir.resolve("Helper.java").toUri().toString();

        settings = new OpenJMLSettings();
        settings.sourcePath = testdir.toString();
        CheckRunner.checkFile(testdir.resolve("Primary.java").toString(), primaryUri, settings);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Find the cursor position for {@code id} within the first occurrence of
     * {@code contextString} in {@code source}, then call
     * {@link Renamer#rename}.
     */
    protected WorkspaceEdit renameAt(String uri, String source,
                                     String contextString, String id, String newName) {
        int lineStart = source.indexOf(contextString);
        assertTrue("Context string not found: «" + contextString + "»", lineStart >= 0);
        int idPos = source.indexOf(id, lineStart);
        assertTrue("Identifier «" + id + "» not found after context string", idPos >= 0);

        int[] lc = DefinitionFinder.offsetToLineCol(source, idPos);
        return Renamer.rename(
                uri, lc[0], lc[1], newName,
                Map.of(primaryUri, primarySrc, helperUri, helperSrc),
                CheckRunner.getASTCache(),
                settings, null);
    }

    /**
     * Apply all edits in {@code edit} to the original sources and return a
     * map of URI → modified source.
     */
    protected Map<String, String> applyEdit(WorkspaceEdit edit) {
        Map<String, String> originals = new HashMap<>();
        originals.put(primaryUri, primarySrc);
        originals.put(helperUri, helperSrc);

        Map<String, String> result = new HashMap<>(originals);
        if (edit.getChanges() == null) return result;

        for (Map.Entry<String, List<TextEdit>> entry : edit.getChanges().entrySet()) {
            String fileUri = entry.getKey();
            String original = originals.get(fileUri);
            if (original == null) continue;
            String modified = Renamer.applyEdits(original, entry.getValue());
            result.put(fileUri, modified);
        }
        return result;
    }

    /**
     * Run {@code --check} on the modified sources and return all diagnostics.
     */
    protected List<Diagnostic> validateModified(Map<String, String> modified) {
        return CheckRunner.checkModifiedFiles(modified, settings);
    }

    /** Assert that the diagnostics list contains no errors. */
    protected void assertNoErrors(List<Diagnostic> diags) {
        assertTrue("Expected no diagnostics after rename but got: " + diags, diags.isEmpty());
    }
}
