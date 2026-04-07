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
// and testRenameNoFalsePositiveOnSafeRename exercise the reference stability check
// added to Renamer.rename().

/**
 * Rename tests — group 4: empty-string abort, reference-stability capture
 * detection, and non-symbol position rejection.
 *
 * <p>Cross-file, pre-existing-error, and keyword/invalid-identifier abort tests
 * are in {@link RenameTest3}.
 *
 * @see RenameTestBase
 */
public class RenameTest4 extends RenameTestBase {

    @Test
    public void testRenameToEmptyStringAborts() {
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

    /**
     * Rename parameter {@code yy} to {@code xx} in a class that already has a
     * field {@code xx}.  Before the rename, {@code yy} has exactly one reference
     * (its own declaration).  After the rename, the body statement {@code int j = xx}
     * (which previously resolved to the field) would start referring to the renamed
     * parameter — the renamed symbol gains a reference.  The stability check must
     * detect the count increase (1 to 2) and reject the rename.
     */
    @Test
    public void testRenameParameterShadowingField() {
        String uri = "file:///tmp/CaptureD.java";
        String src =
                "public class CaptureD {\n"
                + "    int xx;\n"
                + "    public void m(int yy) {\n"
                + "        int j = xx;\n"
                + "    }\n"
                + "}\n";

        OpenJMLSettings s = new OpenJMLSettings();
        CheckRunner.check(uri, src, s);

        int[] lc = DefinitionFinder.offsetToLineCol(src, src.indexOf("int yy") + 4);

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
     * resolves to the local — the renamed symbol gains a reference (2 to 3).
     * The stability check must detect the count increase and reject the rename.
     */
    @Test
    public void testRenameFieldCaptureChangesCount() {
        String uri = "file:///tmp/CaptureE.java";
        String src =
                "public class CaptureE {\n"
                + "    int xx;\n"
                + "    public void m() {\n"
                + "        int aa = 0;\n"
                + "        int j = aa;\n"
                + "        int k = xx;\n"
                + "    }\n"
                + "}\n";

        OpenJMLSettings s = new OpenJMLSettings();
        CheckRunner.check(uri, src, s);

        int[] lc = DefinitionFinder.offsetToLineCol(src, src.indexOf("int aa") + 4);

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
     * {@code bb} symbol in scope.  This is a clean rename: reference count and
     * positions are unchanged.  The stability check must NOT reject this rename.
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

        int[] lc = DefinitionFinder.offsetToLineCol(src, src.indexOf("int aa") + 4);

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
        String context = "//@ requires pJavaField";
        int contextPos = primarySrc.indexOf(context);
        assertTrue("Context string not found in source", contextPos >= 0);
        int atPos = contextPos + 2; // '@' character — not a Java identifier
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
