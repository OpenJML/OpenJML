package org.openjml.lsp.test;

import org.eclipse.lsp4j.WorkspaceEdit;
import org.junit.Test;

import java.util.Map;

import static org.junit.Assert.*;

/**
 * Rename tests hypothesized to be redundant with RenameJmlTest scenarios 1 and 2:
 * renaming a plain Java field and a ghost field declared in a .java file with no
 * .jml companion.  Separated from {@link RenameTest1} so JaCoCo can measure
 * whether these methods add any unique coverage beyond what RenameJmlTest already
 * provides.
 *
 * @see RenameTestBase
 */
public class RenameTest1Maybe extends RenameTestBase {

    @Test
    public void testRenameJavaField() {
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
}
