package org.openjml.lsp.test;

import org.eclipse.lsp4j.WorkspaceEdit;
import org.junit.Test;

import java.util.Map;

import static org.junit.Assert.*;

/**
 * Rename tests for cross-file JML scenarios — scenarios 3 and 4 (aField, ghostInAJml).
 *
 * <p>Uses the four-file test data ({@code testGoToDefinitionJml/}) from
 * {@link RenameJmlTestBase}.  Scenarios 1 and 2 (cField, cGhostField) are in
 * {@link RenameJmlTest}.
 */
public class RenameJmlTest2 extends RenameJmlTestBase {

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
