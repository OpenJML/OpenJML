package org.openjml.lsp.test;

import org.eclipse.lsp4j.WorkspaceEdit;
import org.eclipse.lsp4j.jsonrpc.ResponseErrorException;
import org.junit.Test;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.DefinitionFinder;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.Renamer;

import java.util.Map;

import static org.junit.Assert.*;

// Note: tests testRenameParameterShadowingField, testRenameFieldCaptureChangesCount,
// and testRenameNoFalsePositiveOnSafeRename in this class exercise the reference
// stability check added to Renamer.rename().

/**
 * Rename tests — group 3: cross-file, pre-existing errors, invalid new names.
 *
 * @see RenameTestBase
 */
public class RenameTest3 extends RenameTestBase {

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

    @Test
    public void testRenameToNullLiteralAborts() {
        // "null" is a reserved Java literal — not a valid identifier.
        try {
            renameAt(primaryUri, primarySrc,
                    "requires pJavaField", "pJavaField", "null");
            fail("Expected ResponseErrorException when renaming to 'null'");
        } catch (ResponseErrorException e) {
            assertNotNull(e.getResponseError());
            assertTrue("Error message should mention invalid identifier",
                    e.getResponseError().getMessage().contains("Not a valid Java identifier"));
        }
    }

    @Test
    public void testRenameToEmptyStringAborts() {
        // Renaming to an empty string is not a valid Java identifier.
        // The renamer must reject it with an InvalidParams error rather than
        // silently deleting every occurrence of the symbol.
        try {
            renameAt(primaryUri, primarySrc,
                    "requires pJavaField", "pJavaField", "");
            fail("Expected ResponseErrorException when renaming to empty string");
        } catch (ResponseErrorException e) {
            assertNotNull(e.getResponseError());
            assertTrue("Error message should mention invalid identifier",
                    e.getResponseError().getMessage().contains("Not a valid Java identifier"));
        }
    }

    // -----------------------------------------------------------------------
    // Reference-stability capture tests
    // -----------------------------------------------------------------------

    /**
     * Rename parameter {@code yy} to {@code xx} in a class that already has a
     * field {@code xx}.  Before the rename, {@code yy} has exactly one reference
     * (its own declaration).  After the rename, the body statement {@code int j = xx}
     * (which previously resolved to the field) would start referring to the renamed
     * parameter — the renamed symbol gains a reference.  The stability check must
     * detect the count increase (1 → 2) and reject the rename.
     *
     * <p>The program compiles cleanly both before and after the rename (no new type
     * errors), so the plain error-count check of step 4 does NOT catch this; only
     * the reference stability check of step 4.5 does.
     */
    @Test
    public void testRenameParameterShadowingField() {
        // Class D: field xx; method m(int yy) { int j = xx; }
        // Renaming the parameter yy→xx causes int j = xx to capture the parameter.
        String uri = "file:///tmp/CaptureD.java";
        String src =
                "public class CaptureD {\n"
                + "    int xx;\n"
                + "    public void m(int yy) {\n"
                + "        int j = xx;\n"     // currently references field xx
                + "    }\n"
                + "}\n";

        OpenJMLSettings s = new OpenJMLSettings();
        CheckRunner.check(uri, src, s);   // populate AST cache

        // Place cursor on "yy" in the parameter declaration.
        int[] lc = DefinitionFinder.offsetToLineCol(src, src.indexOf("int yy") + 4); // "yy"

        try {
            Renamer.rename(uri, lc[0], lc[1], "xx",
                    Map.of(uri, src), CheckRunner.getASTCache(), s);
            fail("Expected ResponseErrorException: rename should be rejected because "
                    + "the renamed parameter would capture the body reference to field xx");
        } catch (ResponseErrorException e) {
            assertNotNull(e.getResponseError());
            assertTrue("Error message should mention reference capture",
                    e.getResponseError().getMessage().contains("capture or lose references"));
        }
    }

    /**
     * Rename local variable {@code aa} to {@code xx} in a method that also
     * references a field named {@code xx}.  The local variable has two references
     * (declaration + one body use).  After the rename the local {@code xx} shadows
     * the field, so the body reference that previously resolved to the field now
     * resolves to the local — the renamed symbol gains a reference (2 → 3).
     * The stability check must detect the count increase and reject the rename.
     */
    @Test
    public void testRenameFieldCaptureChangesCount() {
        String uri = "file:///tmp/CaptureE.java";
        String src =
                "public class CaptureE {\n"
                + "    int xx;\n"
                + "    public void m() {\n"
                + "        int aa = 0;\n"     // local aa: 2 refs (decl + j=aa)
                + "        int j = aa;\n"     // use of aa
                + "        int k = xx;\n"     // use of field xx — would be captured
                + "    }\n"
                + "}\n";

        OpenJMLSettings s = new OpenJMLSettings();
        CheckRunner.check(uri, src, s);

        // Place cursor on "aa" in the declaration "int aa = 0".
        int[] lc = DefinitionFinder.offsetToLineCol(src, src.indexOf("int aa") + 4); // "aa"

        try {
            Renamer.rename(uri, lc[0], lc[1], "xx",
                    Map.of(uri, src), CheckRunner.getASTCache(), s);
            fail("Expected ResponseErrorException: field xx reference would be captured");
        } catch (ResponseErrorException e) {
            assertNotNull(e.getResponseError());
            assertTrue("Error message should mention reference capture",
                    e.getResponseError().getMessage().contains("capture or lose references"));
        }
    }

    /**
     * Rename local variable {@code aa} to {@code bb} in a class with no existing
     * {@code bb} symbol in scope.  This is a clean rename: the reference count
     * and positions are unchanged (modulo the expected column shift for the
     * shorter/longer name).  The stability check must NOT reject this rename
     * (regression guard against false positives).
     */
    @Test
    public void testRenameNoFalsePositiveOnSafeRename() {
        String uri = "file:///tmp/SafeRenameF.java";
        String src =
                "public class SafeRenameF {\n"
                + "    public void m() {\n"
                + "        int aa = 0;\n"
                + "        int j = aa;\n"
                + "    }\n"
                + "}\n";

        OpenJMLSettings s = new OpenJMLSettings();
        CheckRunner.check(uri, src, s);

        // Place cursor on "aa" in the declaration.
        int[] lc = DefinitionFinder.offsetToLineCol(src, src.indexOf("int aa") + 4); // "aa"

        // Rename aa → bb: no field bb exists, so no capture possible.
        WorkspaceEdit edit = Renamer.rename(uri, lc[0], lc[1], "bb",
                Map.of(uri, src), CheckRunner.getASTCache(), s);

        assertNotNull("Safe rename must succeed", edit);
        assertNotNull("Edit must have changes", edit.getChanges());
        assertFalse("Edit must not be empty", edit.getChanges().isEmpty());

        String modified = Renamer.applyEdits(src, edit.getChanges().get(uri));
        assertTrue("Modified source must contain new name", modified.contains("bb"));
        assertFalse("Modified source must not contain old name", modified.contains(" aa"));
    }

    @Test
    public void testRenameAtNonSymbolPositionAborts() {
        // Placing the cursor inside a comment or on whitespace means there is no
        // renameable symbol.  The renamer must reject the request rather than
        // returning an empty (silently no-op) edit.
        //
        // We position the cursor on the "@" character of the "//@ requires" comment
        // leader — this is not part of any Java identifier.
        String context = "//@ requires pJavaField";
        int contextPos = primarySrc.indexOf(context);
        assertTrue("Context string not found in source", contextPos >= 0);
        // In "//@ requires ...", the '@' is at index 2 (0-indexed).
        // '@' is not a Java identifier character, so no symbol will be found.
        int atPos = contextPos + 2; // "//@ " → index 2 is '@'
        int[] lc = DefinitionFinder.offsetToLineCol(primarySrc, atPos);

        try {
            Renamer.rename(
                    primaryUri, lc[0], lc[1], "newName",
                    Map.of(primaryUri, primarySrc, helperUri, helperSrc),
                    CheckRunner.getASTCache(),
                    settings);
            fail("Expected ResponseErrorException when cursor is not on a symbol");
        } catch (ResponseErrorException e) {
            assertNotNull(e.getResponseError());
            assertTrue("Error message should mention no renameable symbol",
                    e.getResponseError().getMessage().contains("No renameable symbol"));
        }
    }
}
