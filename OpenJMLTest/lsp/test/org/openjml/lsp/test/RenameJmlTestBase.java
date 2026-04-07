package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.TextEdit;
import org.eclipse.lsp4j.WorkspaceEdit;
import org.junit.Before;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.DefinitionFinder;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.Renamer;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Shared infrastructure for {@link RenameJmlTest} and {@link RenameJmlTest2}.
 *
 * <p>Test data: {@code OpenJMLTest/lsp/testdata/testGoToDefinitionJml/} (shared
 * with {@link DefinitionFinderJmlTest} and {@link ReferenceFinderJmlTest}).
 */
public abstract class RenameJmlTestBase extends LspTestBase {

    protected Path testdir;
    protected String aUri, aJmlUri, bUri, cUri;
    protected String aSrc, aJmlSrc, bSrc, cSrc;
    protected Map<String, String> openContent;
    protected OpenJMLSettings settings;

    @Before
    public void setUp() throws Exception {
        String root = System.getProperty("lsp.testdata");
        assertNotNull("System property lsp.testdata must be set", root);
        testdir = Path.of(root, "testGoToDefinitionJml");
        assertTrue("testGoToDefinitionJml directory must exist",
                testdir.toFile().isDirectory());

        aSrc    = Files.readString(testdir.resolve("A.java"));
        aJmlSrc = Files.readString(testdir.resolve("A.jml"));
        bSrc    = Files.readString(testdir.resolve("B.java"));
        cSrc    = Files.readString(testdir.resolve("C.java"));

        aUri    = testdir.resolve("A.java").toUri().toString();
        aJmlUri = testdir.resolve("A.jml").toUri().toString();
        bUri    = testdir.resolve("B.java").toUri().toString();
        cUri    = testdir.resolve("C.java").toUri().toString();

        openContent = Map.of(aUri, aSrc, aJmlUri, aJmlSrc, bUri, bSrc, cUri, cSrc);

        settings = new OpenJMLSettings();
        settings.sourcePath = testdir.toString();

        // Compile B.java with sourcepath so A.java, A.jml, C.java are pulled in.
        CheckRunner.checkFile(testdir.resolve("B.java").toString(), bUri, settings);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    protected WorkspaceEdit renameAt(String uri, String source,
                                     String ctx, String id, String newName) {
        int lineStart = source.indexOf(ctx);
        assertTrue("Context «" + ctx + "» not found in source", lineStart >= 0);
        int idPos = source.indexOf(id, lineStart);
        assertTrue("Identifier «" + id + "» not found after context", idPos >= 0);
        int[] lc = DefinitionFinder.offsetToLineCol(source, idPos);
        return Renamer.rename(uri, lc[0], lc[1], newName, openContent,
                CheckRunner.getASTCache(), settings);
    }

    protected Map<String, String> applyEdit(WorkspaceEdit edit) {
        Map<String, String> result = new HashMap<>(openContent);
        if (edit == null || edit.getChanges() == null) return result;
        for (Map.Entry<String, List<TextEdit>> e : edit.getChanges().entrySet()) {
            String fileUri = e.getKey();
            String original = openContent.get(fileUri);
            if (original == null) continue;
            result.put(fileUri, Renamer.applyEdits(original, e.getValue()));
        }
        return result;
    }

    protected void assertEditHasFile(WorkspaceEdit edit, String uri) {
        assertNotNull("WorkspaceEdit must not be null", edit);
        assertNotNull("WorkspaceEdit.changes must not be null", edit.getChanges());
        assertTrue("Edit must include file " + new File(uri).getName(),
                edit.getChanges().containsKey(uri)
                        && !edit.getChanges().get(uri).isEmpty());
    }

    protected void assertContains(Map<String, String> modified, String uri, String text) {
        String src = modified.get(uri);
        assertNotNull("No source for " + new File(uri).getName(), src);
        assertTrue("Expected «" + text + "» in " + new File(uri).getName(),
                src.contains(text));
    }

    protected void validateModified(Map<String, String> modified) {
        List<Diagnostic> diags = CheckRunner.checkModifiedFiles(modified, settings);
        assertTrue("Expected no diagnostics after rename but got: " + diags,
                diags.isEmpty());
    }
}
