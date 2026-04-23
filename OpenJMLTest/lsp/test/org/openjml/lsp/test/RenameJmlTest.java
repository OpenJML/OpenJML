package org.openjml.lsp.test;

import org.eclipse.lsp4j.WorkspaceEdit;
import org.junit.Test;

import java.util.Map;

import static org.junit.Assert.*;

/**
 * Rename tests for cross-file JML scenarios — scenarios 1 and 2 (cField, cGhostField).
 *
 * <p>Uses the four-file test data ({@code testGoToDefinitionJml/}) from
 * {@link RenameJmlTestBase}.  Scenarios 3 and 4 (aField, ghostInAJml) are in
 * {@link RenameJmlTest2}.
 *
 * <p>Each test renames a symbol from a given cursor position and verifies:
 * <ol>
 *   <li>The {@link WorkspaceEdit} covers all expected files.</li>
 *   <li>Applying the edits produces sources that contain the new name and not
 *       the old one (at the expected sites).</li>
 *   <li>{@code --check} on the modified sources produces no new errors.</li>
 * </ol>
 */
public class RenameJmlTest extends RenameJmlTestBase {

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
}
