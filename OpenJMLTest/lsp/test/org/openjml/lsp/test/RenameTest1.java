package org.openjml.lsp.test;

import org.eclipse.lsp4j.WorkspaceEdit;
import org.junit.Test;

import java.util.Map;

import static org.junit.Assert.*;

/**
 * Rename tests — group 1: Java/ghost/model fields and methods.
 *
 * @see RenameTestBase
 */
public class RenameTest1 extends RenameTestBase {

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

}
