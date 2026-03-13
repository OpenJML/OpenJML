package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.TextEdit;
import org.eclipse.lsp4j.WorkspaceEdit;
import org.eclipse.lsp4j.jsonrpc.ResponseErrorException;
import org.junit.Before;
import org.junit.Test;
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
 * Tests for {@link Renamer}: symbol rename with validation.
 *
 * <p>Test data: {@code OpenJMLTest/lsp/testdata/testGoToDefinition/} (shared
 * with {@link DefinitionFinderTest}).
 *
 * <p>Each test uses a DIFFERENT-LENGTH new name to make it easy to detect
 * that the rename actually changed text rather than leaving the old name in place.
 */
public class RenameTest {

    private Path testdir;
    private String primaryUri, helperUri;
    private String primarySrc, helperSrc;
    private OpenJMLSettings settings;

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
    private WorkspaceEdit renameAt(String uri, String source,
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
                settings);
    }

    /**
     * Apply all edits in {@code edit} to the original sources and return a
     * map of URI → modified source.
     */
    private Map<String, String> applyEdit(WorkspaceEdit edit) {
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
    private List<Diagnostic> validateModified(Map<String, String> modified) {
        return CheckRunner.checkModifiedFiles(modified, settings);
    }

    /** Assert that the diagnostics list contains no errors. */
    private void assertNoErrors(List<Diagnostic> diags) {
        assertTrue("Expected no diagnostics after rename but got: " + diags, diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    @Test
    public void testRenameJavaField() {
        // Rename pJavaField → pXJavaFieldRenamed (longer)
        WorkspaceEdit edit = renameAt(primaryUri, primarySrc,
                "requires pJavaField", "pJavaField", "pXJavaFieldRenamed");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String p = modified.get(primaryUri);
        assertTrue("modified primary must contain new name",
                p.contains("pXJavaFieldRenamed"));
        assertFalse("modified primary must not contain old name in requires clause",
                p.contains("requires pJavaField"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameGhostField() {
        // Rename pGhostField → gf (shorter)
        WorkspaceEdit edit = renameAt(primaryUri, primarySrc,
                "requires pGhostField", "pGhostField", "gf");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String p = modified.get(primaryUri);
        assertTrue("modified primary must contain new name", p.contains("gf"));
        assertFalse("modified primary must not contain old name in requires clause",
                p.contains("requires pGhostField"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameModelField() {
        // Rename pModelField → pMFX (shorter)
        WorkspaceEdit edit = renameAt(primaryUri, primarySrc,
                "requires pModelField", "pModelField", "pMFX");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String p = modified.get(primaryUri);
        assertTrue("modified primary must contain new name", p.contains("pMFX"));
        assertFalse("modified primary must not contain old name in requires clause",
                p.contains("requires pModelField"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameJavaMethod() {
        // Rename pJavaMethod → pJM (shorter)
        WorkspaceEdit edit = renameAt(primaryUri, primarySrc,
                "requires pJavaMethod", "pJavaMethod", "pJM");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String p = modified.get(primaryUri);
        assertTrue("modified primary must contain new name", p.contains("pJM"));
        assertFalse("modified primary must not contain old name in requires clause",
                p.contains("requires pJavaMethod"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameModelMethod() {
        // Rename pModelMethod → pMMXYZ (longer)
        WorkspaceEdit edit = renameAt(primaryUri, primarySrc,
                "requires pModelMethod", "pModelMethod", "pMMXYZ");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String p = modified.get(primaryUri);
        assertTrue("modified primary must contain new name", p.contains("pMMXYZ"));
        assertFalse("modified primary must not contain old name in requires clause",
                p.contains("requires pModelMethod"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameModelClass() {
        // Rename PModelClass → PMC2Longer (longer)
        // Cursor at the class name in its own declaration.
        WorkspaceEdit edit = renameAt(primaryUri, primarySrc,
                "model public class PModelClass", "PModelClass", "PMC2Longer");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String p = modified.get(primaryUri);
        assertTrue("modified primary must contain new class name",
                p.contains("PMC2Longer"));
        // The type use in "ghost public PModelClass pModelInst" must also be renamed.
        assertFalse("type use of PModelClass must be renamed",
                p.contains("PModelClass"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameForallBoundVar() {
        // Rename forall bound var i → loopIdx (longer)
        // Cursor at the use site "i < pJavaField".
        WorkspaceEdit edit = renameAt(primaryUri, primarySrc,
                "i < pJavaField", "i", "loopIdx");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String p = modified.get(primaryUri);
        assertTrue("modified primary must contain \"forall int loopIdx\"",
                p.contains("forall int loopIdx"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameLetVar() {
        // Rename letVar → lv (shorter)
        // Cursor at use: "letVar >= 0".
        WorkspaceEdit edit = renameAt(primaryUri, primarySrc,
                "letVar >= 0", "letVar", "lv");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String p = modified.get(primaryUri);
        assertTrue("modified primary must contain \"\\let int lv\"",
                p.contains("\\let int lv"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameExistsBoundVar() {
        // Rename qi → qiNew (longer)
        // Cursor at use: "qi < qj".
        WorkspaceEdit edit = renameAt(primaryUri, primarySrc,
                "qi < qj", "qi", "qiNew");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String p = modified.get(primaryUri);
        assertTrue("modified primary must contain \"qiNew < qj\"",
                p.contains("qiNew < qj"));
        // qj must be unchanged.
        assertTrue("qj must still be present unchanged", p.contains("qj"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameFormalParameter() {
        // Rename parameter x in pJavaMethod → paramX (longer)
        // Cursor at "requires x >= 0".
        WorkspaceEdit edit = renameAt(primaryUri, primarySrc,
                "requires x >= 0", "x", "paramX");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String p = modified.get(primaryUri);
        assertTrue("declaration line must use new param name",
                p.contains("int paramX)") || p.contains("(int paramX"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameCrossFileField() {
        // Rename hJavaField → hJF (shorter)
        // Cursor at the declaration in helperSrc.
        WorkspaceEdit edit = renameAt(helperUri, helperSrc,
                "public int hJavaField", "hJavaField", "hJF");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        // Both Helper.java and Primary.java should be modified.
        String h = modified.get(helperUri);
        String p = modified.get(primaryUri);
        assertTrue("Helper.java must contain new field name", h.contains("hJF"));
        assertFalse("Helper.java must not contain old field name", h.contains("hJavaField"));
        assertTrue("Primary.java must contain new field name", p.contains("hJF"));
        assertFalse("Primary.java must not contain old field name in requires",
                p.contains("helper.hJavaField"));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameCrossFileMethod() {
        // Rename hJavaMethod → hJavaMethodNew (longer)
        // Cursor at the declaration in helperSrc.
        WorkspaceEdit edit = renameAt(helperUri, helperSrc,
                "public int hJavaMethod", "hJavaMethod", "hJavaMethodNew");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
        String h = modified.get(helperUri);
        String p = modified.get(primaryUri);
        assertTrue("Helper.java must contain new method name", h.contains("hJavaMethodNew"));
        assertFalse("Helper.java must not contain old method name", h.contains("public int hJavaMethod("));
        assertTrue("Primary.java must contain new method name", p.contains("hJavaMethodNew"));
        assertFalse("Primary.java must not contain old method name in requires",
                p.contains("helper.hJavaMethod("));
        assertNoErrors(validateModified(modified));
    }

    @Test
    public void testRenameWithPreexistingJmlError() {
        // A source file with a pre-existing JML error (unknown symbol in invariant).
        // The Java code is valid, so symbols ARE resolved and the rename should
        // succeed: the baseline and modified error counts are equal, so only
        // NEW errors introduced by the rename would block it.
        String errUri = "file:///tmp/PreExistingErr.java";
        String errSrc =
                "public class PreExistingErr {\n"
                + "    public int field = 0;\n"
                + "    //@ invariant noSuchSymbol >= 0;\n"  // pre-existing JML error
                + "    //@ requires field >= 0;\n"
                + "    public int compute(int x) { return field + x; }\n"
                + "}\n";

        OpenJMLSettings s = new OpenJMLSettings();
        CheckRunner.check(errUri, errSrc, s);  // populate AST cache

        // Find cursor on "field" in "requires field >= 0".
        int lineStart = errSrc.indexOf("requires field");
        int idPos = errSrc.indexOf("field", lineStart);
        int[] lc = DefinitionFinder.offsetToLineCol(errSrc, idPos);

        WorkspaceEdit edit = Renamer.rename(
                errUri, lc[0], lc[1], "renamedField",
                Map.of(errUri, errSrc),
                CheckRunner.getASTCache(),
                s);

        assertNotNull("rename must succeed despite pre-existing JML error", edit);
        assertNotNull("edit must have changes", edit.getChanges());
        assertFalse("edit must not be empty", edit.getChanges().isEmpty());
        String modified = Renamer.applyEdits(errSrc, edit.getChanges().get(errUri));
        assertTrue("modified must contain new name", modified.contains("renamedField"));
        assertFalse("modified must not contain old requires clause",
                modified.contains("requires field "));
    }

    @Test
    public void testRenameToKeywordAborts() {
        // Renaming to a Java keyword must throw ResponseErrorException.
        try {
            renameAt(primaryUri, primarySrc,
                    "requires pJavaField", "pJavaField", "class");
            fail("Expected ResponseErrorException when renaming to keyword");
        } catch (ResponseErrorException e) {
            // Expected — verify the message is meaningful.
            assertNotNull(e.getResponseError());
            assertTrue("Error message should mention invalid identifier",
                    e.getResponseError().getMessage().contains("Not a valid Java identifier"));
        }
    }

    @Test
    public void testRenameToInvalidIdentAborts() {
        // Renaming to "123bad" (starts with digit) must throw ResponseErrorException.
        try {
            renameAt(primaryUri, primarySrc,
                    "requires pJavaField", "pJavaField", "123bad");
            fail("Expected ResponseErrorException when renaming to invalid identifier");
        } catch (ResponseErrorException e) {
            assertNotNull(e.getResponseError());
            assertTrue("Error message should mention invalid identifier",
                    e.getResponseError().getMessage().contains("Not a valid Java identifier"));
        }
    }
}
