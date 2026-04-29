package org.openjml.lsp.test;

import org.eclipse.lsp4j.WorkspaceEdit;
import org.junit.Test;

import java.util.Map;

import static org.junit.Assert.*;

/**
 * Rename tests — group 2: model class, JML bound variables, formal parameter.
 *
 * @see RenameTestBase
 */
public class RenameTest2 extends RenameTestBase {

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
}
