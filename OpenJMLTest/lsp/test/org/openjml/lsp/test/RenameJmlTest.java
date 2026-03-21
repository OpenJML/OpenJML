package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.TextEdit;
import org.eclipse.lsp4j.WorkspaceEdit;
import org.junit.Before;
import org.junit.Test;
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
 * Rename tests for cross-file JML scenarios, using the same four-file test data
 * ({@code testGoToDefinitionJml/}) as {@link DefinitionFinderJmlTest} and
 * {@link ReferenceFinderJmlTest}.
 *
 * <p>Each test renames a symbol from a given cursor position and verifies:
 * <ol>
 *   <li>The {@link WorkspaceEdit} covers all expected files.</li>
 *   <li>Applying the edits produces sources that contain the new name and not
 *       the old one (at the expected sites).</li>
 *   <li>{@code --check} on the modified sources produces no new errors.</li>
 * </ol>
 *
 * <p>The four scenarios mirror those in {@link DefinitionFinderJmlTest}:
 * <ol>
 *   <li>{@code cField}      — Java field in C.java (no companion .jml)</li>
 *   <li>{@code cGhostField} — JML ghost field in C.java (no companion .jml)</li>
 *   <li>{@code aField}      — Java field in A.java (companion A.jml exists)</li>
 *   <li>{@code ghostInAJml} — JML ghost field declared only in A.jml</li>
 * </ol>
 */
public class RenameJmlTest extends LspTestBase {

    private Path testdir;
    private String aUri, aJmlUri, bUri, cUri;
    private String aSrc, aJmlSrc, bSrc, cSrc;
    private Map<String, String> openContent;
    private OpenJMLSettings settings;

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

    /**
     * Find the cursor position for {@code id} within the first occurrence of
     * {@code ctx} in {@code source}, then invoke {@link Renamer#rename}.
     */
    private WorkspaceEdit renameAt(String uri, String source,
                                   String ctx, String id, String newName) {
        int lineStart = source.indexOf(ctx);
        assertTrue("Context «" + ctx + "» not found in source", lineStart >= 0);
        int idPos = source.indexOf(id, lineStart);
        assertTrue("Identifier «" + id + "» not found after context", idPos >= 0);
        int[] lc = DefinitionFinder.offsetToLineCol(source, idPos);
        return Renamer.rename(uri, lc[0], lc[1], newName, openContent,
                CheckRunner.getASTCache(), settings);
    }

    /**
     * Apply all edits from {@code edit} to the original sources and return the
     * resulting URI → modified-source map (unmodified files keep their original).
     */
    private Map<String, String> applyEdit(WorkspaceEdit edit) {
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

    /** Assert that the edit includes at least one change for {@code uri}. */
    private void assertEditHasFile(WorkspaceEdit edit, String uri) {
        assertNotNull("WorkspaceEdit must not be null", edit);
        assertNotNull("WorkspaceEdit.changes must not be null", edit.getChanges());
        assertTrue("Edit must include file " + new File(uri).getName(),
                edit.getChanges().containsKey(uri)
                        && !edit.getChanges().get(uri).isEmpty());
    }

    /** Assert that the modified source for {@code uri} contains {@code text}. */
    private void assertContains(Map<String, String> modified, String uri, String text) {
        String src = modified.get(uri);
        assertNotNull("No source for " + new File(uri).getName(), src);
        assertTrue("Expected «" + text + "» in " + new File(uri).getName(),
                src.contains(text));
    }

    /**
     * Run {@code --check} on the modified sources and assert no diagnostics.
     */
    private void validateModified(Map<String, String> modified) {
        List<Diagnostic> diags = CheckRunner.checkModifiedFiles(modified, settings);
        assertTrue("Expected no diagnostics after rename but got: " + diags,
                diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Scenario 1: cField — Java field declared in C.java
    // -----------------------------------------------------------------------

    /**
     * Rename {@code cField} from its declaration in C.java.
     * Expected edits in C.java (declaration, spec, body), A.java (body assert),
     * A.jml (invariant, method spec), and B.java (spec, body).
     */
    @Test
    public void s1_cField_renameFromDeclaration() {
        WorkspaceEdit edit = renameAt(cUri, cSrc,
                "public int cField", "cField", "cFieldX");
        assertEditHasFile(edit, cUri);
        assertEditHasFile(edit, aUri);
        assertEditHasFile(edit, aJmlUri);
        assertEditHasFile(edit, bUri);

        Map<String, String> modified = applyEdit(edit);
        assertContains(modified, cUri,    "cFieldX");
        assertContains(modified, aUri,    "cFieldX");
        assertContains(modified, aJmlUri, "cFieldX");
        assertContains(modified, bUri,    "cFieldX");
        validateModified(modified);
    }

    /**
     * Rename {@code cField} from a use in B.java's JML spec — should yield
     * the same edit set as renaming from the declaration.
     */
    @Test
    public void s1_cField_renameFromBjavaSpec() {
        WorkspaceEdit edit = renameAt(bUri, bSrc,
                "requires cObj.cField", "cField", "cFieldY");
        assertEditHasFile(edit, cUri);
        assertEditHasFile(edit, aUri);
        assertEditHasFile(edit, aJmlUri);
        assertEditHasFile(edit, bUri);
        validateModified(applyEdit(edit));
    }

    // -----------------------------------------------------------------------
    // Scenario 2: cGhostField — JML ghost field declared in C.java
    // -----------------------------------------------------------------------

    /**
     * Rename {@code cGhostField} from its ghost declaration in C.java.
     * Expected edits in C.java (declaration, spec), A.java (body assert),
     * A.jml (invariant, method spec), and B.java (spec).
     */
    @Test
    public void s2_cGhostField_renameFromDeclaration() {
        WorkspaceEdit edit = renameAt(cUri, cSrc,
                "ghost public int cGhostField", "cGhostField", "cGhostX");
        assertEditHasFile(edit, cUri);
        assertEditHasFile(edit, aUri);
        assertEditHasFile(edit, aJmlUri);
        assertEditHasFile(edit, bUri);

        Map<String, String> modified = applyEdit(edit);
        assertContains(modified, cUri,    "cGhostX");
        assertContains(modified, aUri,    "cGhostX");
        assertContains(modified, aJmlUri, "cGhostX");
        assertContains(modified, bUri,    "cGhostX");
        validateModified(modified);
    }

    /**
     * Rename {@code cGhostField} from its use in A.jml's invariant.
     */
    @Test
    public void s2_cGhostField_renameFromAjmlInvariant() {
        WorkspaceEdit edit = renameAt(aJmlUri, aJmlSrc,
                "invariant cObj.cGhostField", "cGhostField", "cGhostY");
        assertEditHasFile(edit, cUri);
        assertEditHasFile(edit, aUri);
        assertEditHasFile(edit, aJmlUri);
        assertEditHasFile(edit, bUri);
        validateModified(applyEdit(edit));
    }

    // -----------------------------------------------------------------------
    // Scenario 3: aField — Java field in A.java with companion A.jml
    // -----------------------------------------------------------------------

    /**
     * Rename {@code aField} from its declaration in A.java.
     * Expected edits in A.java (declaration, body), A.jml (spec stub, invariant,
     * method spec), and B.java (spec, body).
     * The hidden inline spec in A.java ({@code //@ requires aField >= 0;}) is
     * NOT attributed so it is not in the references list and will not be renamed;
     * the compiler ignores that hidden spec, so {@code --check} still passes.
     */
    @Test
    public void s3_aField_renameFromDeclaration() {
        WorkspaceEdit edit = renameAt(aUri, aSrc,
                "public int aField = 0", "aField", "aFieldX");
        assertEditHasFile(edit, aUri);
        assertEditHasFile(edit, aJmlUri);
        assertEditHasFile(edit, bUri);

        Map<String, String> modified = applyEdit(edit);
        assertContains(modified, aUri,    "aFieldX");
        assertContains(modified, aJmlUri, "aFieldX");
        assertContains(modified, bUri,    "aFieldX");
        validateModified(modified);
    }

    /**
     * Rename {@code aField} from a use in A.jml's invariant — same edit set.
     */
    @Test
    public void s3_aField_renameFromAjmlInvariant() {
        WorkspaceEdit edit = renameAt(aJmlUri, aJmlSrc,
                "invariant aField >= 0", "aField", "aFieldY");
        assertEditHasFile(edit, aUri);
        assertEditHasFile(edit, aJmlUri);
        assertEditHasFile(edit, bUri);
        validateModified(applyEdit(edit));
    }

    // -----------------------------------------------------------------------
    // Scenario 4: ghostInAJml — ghost field declared only in A.jml
    // -----------------------------------------------------------------------

    /**
     * Rename {@code ghostInAJml} from its ghost declaration in A.jml.
     * Expected edits in A.jml (declaration, invariant, method spec),
     * A.java (body assert), and B.java (spec).
     */
    @Test
    public void s4_ghostInAJml_renameFromDeclaration() {
        WorkspaceEdit edit = renameAt(aJmlUri, aJmlSrc,
                "ghost public int ghostInAJml", "ghostInAJml", "ghostX");
        assertEditHasFile(edit, aJmlUri);
        assertEditHasFile(edit, aUri);
        assertEditHasFile(edit, bUri);

        Map<String, String> modified = applyEdit(edit);
        assertContains(modified, aJmlUri, "ghostX");
        assertContains(modified, aUri,    "ghostX");
        assertContains(modified, bUri,    "ghostX");
        validateModified(modified);
    }

    /**
     * Rename {@code ghostInAJml} from a use in B.java's JML spec.
     */
    @Test
    public void s4_ghostInAJml_renameFromBjavaSpec() {
        WorkspaceEdit edit = renameAt(bUri, bSrc,
                "requires aObj.ghostInAJml", "ghostInAJml", "ghostY");
        assertEditHasFile(edit, aJmlUri);
        assertEditHasFile(edit, aUri);
        assertEditHasFile(edit, bUri);
        validateModified(applyEdit(edit));
    }
}
