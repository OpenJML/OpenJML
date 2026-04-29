package org.openjml.lsp.test;

import org.eclipse.lsp4j.DiagnosticSeverity;
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
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * Rename tests for method and class symbols, using the {@code testMethodClass/}
 * test data (IWorker, WorkerA, WorkerB, Manager).
 *
 * <p>Extracted from {@link MethodAndClassTest} so rename scenarios live with the
 * other rename test suites.  The go-to-definition and find-references tests for
 * method/class symbols remain in {@link MethodAndClassTest}.
 */
public class RenameMethodAndClassTest extends LspTestBase {

    private Path testdir;
    private String iWorkerUri, workerAUri, workerBUri, managerUri;
    private String iWorkerSrc, workerASrc, workerBSrc, managerSrc;
    private Map<String, String> openContent;
    private OpenJMLSettings settings;

    @Before
    public void setUp() throws Exception {
        String root = System.getProperty("lsp.testdata");
        assertNotNull("System property lsp.testdata must be set", root);
        testdir = Path.of(root, "testMethodClass");
        assertTrue("testMethodClass directory must exist", testdir.toFile().isDirectory());

        iWorkerSrc = Files.readString(testdir.resolve("IWorker.java"));
        workerASrc = Files.readString(testdir.resolve("WorkerA.java"));
        workerBSrc = Files.readString(testdir.resolve("WorkerB.java"));
        managerSrc = Files.readString(testdir.resolve("Manager.java"));

        iWorkerUri = testdir.resolve("IWorker.java").toUri().toString();
        workerAUri = testdir.resolve("WorkerA.java").toUri().toString();
        workerBUri = testdir.resolve("WorkerB.java").toUri().toString();
        managerUri = testdir.resolve("Manager.java").toUri().toString();

        openContent = Map.of(
                iWorkerUri, iWorkerSrc,
                workerAUri, workerASrc,
                workerBUri, workerBSrc,
                managerUri, managerSrc);

        settings = new OpenJMLSettings();
        settings.sourcePath = testdir.toString();
        CheckRunner.checkFile(testdir.resolve("Manager.java").toString(), managerUri, settings);
    }

    // -----------------------------------------------------------------------
    // Rename: concrete method with no interface override (succeeds)
    // -----------------------------------------------------------------------

    @Test
    public void testRenameConcreteMethodSucceeds() {
        WorkspaceEdit edit = renameAt(workerAUri, workerASrc,
                "public int doubleWork", "doubleWork", "computeDouble");
        assertNotNull("Rename of non-override method must succeed", edit);
        assertNotNull("WorkspaceEdit must have changes", edit.getChanges());
        assertTrue("Edit must update WorkerA.java", edit.getChanges().containsKey(workerAUri));
        assertTrue("Edit must update Manager.java",  edit.getChanges().containsKey(managerUri));

        Map<String, String> modified = applyEdit(edit);
        assertTrue("WorkerA.java must contain new method name",
                modified.get(workerAUri).contains("public int computeDouble"));
        assertFalse("WorkerA.java declaration must not contain old method name",
                modified.get(workerAUri).contains("public int doubleWork"));
        assertTrue("Manager.java must contain new call",
                modified.get(managerUri).contains(".computeDouble("));
        assertFalse("Manager.java must not contain old call",
                modified.get(managerUri).contains(".doubleWork("));
        assertNoErrors(CheckRunner.checkModifiedFiles(modified, settings));
    }

    // -----------------------------------------------------------------------
    // Rename: interface method (rejected — override declarations not found)
    // -----------------------------------------------------------------------

    @Test
    public void testRenameInterfaceMethodIsRejectedDueToMissingOverrideUpdate() {
        try {
            renameAt(iWorkerUri, iWorkerSrc, "int doWork", "doWork", "runWork");
            fail("Expected rename to be rejected: implementations retain 'doWork' but "
                    + "interface is renamed 'runWork', breaking the contract");
        } catch (ResponseErrorException e) {
            assertNotNull(e.getResponseError());
            String msg = e.getResponseError().getMessage();
            assertTrue("Error must indicate that errors were introduced: " + msg,
                    msg.contains("introduce errors") || msg.contains("capture or lose"));
        }
    }

    @Test
    public void testRenameImplementationMethodIsRejectedDueToMissingInterfaceUpdate() {
        try {
            renameAt(workerAUri, workerASrc, "public int doWork", "doWork", "workerATask");
            fail("Expected rename to be rejected: WorkerA would no longer implement IWorker.doWork");
        } catch (ResponseErrorException e) {
            assertNotNull(e.getResponseError());
            String msg = e.getResponseError().getMessage();
            assertTrue("Error must indicate that errors were introduced: " + msg,
                    msg.contains("introduce errors") || msg.contains("capture or lose"));
        }
    }

    // -----------------------------------------------------------------------
    // Rename: class names
    // -----------------------------------------------------------------------

    @Test
    public void testRenamePublicClassIsRejectedDueToFilenameConstraint() {
        try {
            renameAt(workerAUri, workerASrc, "public class WorkerA", "WorkerA", "WorkerAlpha");
            fail("Expected rename to be rejected: public class name must match filename");
        } catch (ResponseErrorException e) {
            assertNotNull(e.getResponseError());
            String msg = e.getResponseError().getMessage();
            assertTrue("Error must mention the filename constraint or new errors: " + msg,
                    msg.contains("introduce errors") || msg.contains("WorkerAlpha")
                    || msg.contains("file"));
        }
    }

    @Test
    public void testRenamePrivateFieldInClassSucceeds() {
        WorkspaceEdit edit = renameAt(workerAUri, workerASrc, "private int count", "count", "total");
        assertNotNull("Private field rename must succeed", edit);
        assertNotNull("Edit must have changes", edit.getChanges());
        assertTrue("Edit must include WorkerA.java", edit.getChanges().containsKey(workerAUri));

        Map<String, String> modified = applyEdit(edit);
        assertTrue("WorkerA must contain new field name", modified.get(workerAUri).contains("total"));
        assertFalse("WorkerA must not contain old field name",
                modified.get(workerAUri).contains("private int count"));
        assertNoErrors(CheckRunner.checkModifiedFiles(modified, settings));
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private WorkspaceEdit renameAt(String uri, String source, String ctx, String id, String newName) {
        int ctxPos = source.indexOf(ctx);
        assertTrue("Context «" + ctx + "» not found", ctxPos >= 0);
        int idPos = source.indexOf(id, ctxPos);
        assertTrue("Identifier «" + id + "» not found after context", idPos >= 0);
        int[] lc = DefinitionFinder.offsetToLineCol(source, idPos);
        return Renamer.rename(uri, lc[0], lc[1], newName, openContent, CheckRunner.getASTCache(), settings, null);
    }

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

    private void assertNoErrors(List<org.eclipse.lsp4j.Diagnostic> diags) {
        List<org.eclipse.lsp4j.Diagnostic> errors = diags.stream()
                .filter(d -> d.getSeverity() == DiagnosticSeverity.Error)
                .collect(Collectors.toList());
        assertTrue("Expected no error diagnostics after rename but got: " + errors, errors.isEmpty());
    }
}
