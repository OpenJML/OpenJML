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

/**
 * Rename tests — group 3: cross-file, pre-existing errors, keyword/invalid aborts.
 *
 * <p>Reference-stability capture tests and the remaining abort tests are in
 * {@link RenameTest4}.
 *
 * @see RenameTestBase
 */
public class RenameTest3 extends RenameTestBase {

    @Test
    public void testRenameCrossFileField() {
        WorkspaceEdit edit = renameAt(helperUri, helperSrc,
                "public int hJavaField", "hJavaField", "hJF");
        assertNotNull(edit);
        Map<String, String> modified = applyEdit(edit);
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
        String errUri = "file:///tmp/PreExistingErr.java";
        String errSrc =
                "public class PreExistingErr {\n"
                + "    public int field = 0;\n"
                + "    //@ invariant noSuchSymbol >= 0;\n"
                + "    //@ requires field >= 0;\n"
                + "    public int compute(int x) { return field + x; }\n"
                + "}\n";

        OpenJMLSettings s = new OpenJMLSettings();
        CheckRunner.check(errUri, errSrc, s);

        int lineStart = errSrc.indexOf("requires field");
        int idPos = errSrc.indexOf("field", lineStart);
        int[] lc = DefinitionFinder.offsetToLineCol(errSrc, idPos);

        // Use renameWithErrors() so the pre-existing JML error is returned rather
        // than causing a hard rejection.  The edit is still computed; only the
        // pre-existing "noSuchSymbol" error appears in the errors list.
        Renamer.RenameResponse resp = Renamer.renameWithErrors(
                errUri, lc[0], lc[1], "renamedField",
                Map.of(errUri, errSrc),
                CheckRunner.getASTCache(),
                s, null);

        WorkspaceEdit edit = resp.edit();
        assertNotNull("rename must produce an edit despite pre-existing JML error", edit);
        assertNotNull("edit must have changes", edit.getChanges());
        assertFalse("edit must not be empty", edit.getChanges().isEmpty());
        String modified = Renamer.applyEdits(errSrc, edit.getChanges().get(errUri));
        assertTrue("modified must contain new name", modified.contains("renamedField"));
        assertFalse("modified must not contain old requires clause",
                modified.contains("requires field "));
    }

    @Test
    public void testRenameToKeywordAborts() {
        try {
            renameAt(primaryUri, primarySrc,
                    "requires pJavaField", "pJavaField", "class");
            fail("Expected ResponseErrorException when renaming to keyword");
        } catch (ResponseErrorException e) {
            assertNotNull(e.getResponseError());
            assertTrue("Error message should mention invalid identifier",
                    e.getResponseError().getMessage().contains("Not a valid Java identifier"));
        }
    }

    @Test
    public void testRenameToInvalidIdentAborts() {
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
}
