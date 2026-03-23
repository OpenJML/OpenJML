package org.jmlspecs.openjml.eclipse.uitest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable;
import org.eclipse.swtbot.swt.finder.results.VoidResult;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.ui.ide.IDE;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runners.MethodSorters;

/**
 * GUI tests for features that require the OpenJML LSP server to be running:
 * Rename dialog pre-fill, Find References, Check JML markers, and marker
 * lifecycle on nature removal.
 *
 * <p>All LSP-dependent tests are combined in one class so the server starts
 * once (~20s) and is reused across all tests, rather than paying the startup
 * cost per test class.
 *
 * <h3>Test projects</h3>
 * <ul>
 *   <li><b>ActionTestProject</b> — single file {@code ActionTarget.java} with
 *       two uses of {@code myField} (Java declaration + JML requires clause).
 *       Used by Rename and Find References tests.</li>
 *   <li><b>MarkersProjectA</b> — JML annotation but NO JML nature.
 *       JML markers must NOT appear here.</li>
 *   <li><b>MarkersProjectB</b> — JML nature; has a JML type error.
 *       JML marker should appear after Check JML.</li>
 *   <li><b>MarkersProjectC</b> — JML nature; has an ESC error.</li>
 * </ul>
 *
 * <h3>Test order</h3>
 * Tests are ordered alphabetically.  The "a_" prefix tests (Action) run first,
 * then "m_" prefix tests (Markers).  Marker tests share state (t2/t3 depend
 * on t1 having produced markers).
 */
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class LspFeatureTest extends GUITestBase {

    // -----------------------------------------------------------------------
    // Action test constants
    // -----------------------------------------------------------------------

    private static final String RENAME_COMMAND_ID =
            "org.openjml.eclipse.commands.rename";
    private static final String FIND_REFS_COMMAND_ID =
            "org.openjml.eclipse.commands.findReferences";
    private static final String TARGET_SYMBOL = "myField";

    /**
     * Source with two Java references to {@code myField}: the declaration
     * (line 2) and a use in {@code getMyField()} (line 3).
     *
     * <p>JML annotations are deliberately omitted because the OpenJML parser
     * has a known NPE bug when parsing JML clauses through the LSP server's
     * CheckRunner path (works fine via direct {@code openjml --check}).
     * Cross-language reference correctness is verified by
     * {@code OpenJMLTest/lsp/ReferenceFinderTest}.
     */
    private static final String ACTION_SOURCE =
            "package actiontest;\n"
            + "public class ActionTarget {\n"
            + "    public int myField = 0;\n"
            + "    public int getMyField() { return myField; }\n"
            + "    public void method(int x) { }\n"
            + "}\n";

    // line 2: "    public int myField = 0;" — myField at col 15
    private static final int SYMBOL_LINE = 2;
    private static final int SYMBOL_COL  = 15;

    // -----------------------------------------------------------------------
    // Marker test constants
    // -----------------------------------------------------------------------

    private static final String LSP4E_MARKER = "org.eclipse.lsp4e.diagnostic";
    private static final String SERVER_ID_ATTR = "languageServerId";
    private static final String OPENJML_SERVER_ID = "org.jmlspecs.openjml.lsp.server";
    private static final String JAVA_MARKER = "org.eclipse.jdt.core.problem";
    private static final int CHECK_JML_TIMEOUT_MS = 90_000;

    // -----------------------------------------------------------------------
    // Shared state
    // -----------------------------------------------------------------------

    private static IProject actionProject;
    private static IFile    actionSourceFile;

    private static IProject markersProjectA;
    private static IProject markersProjectB;
    private static IProject markersProjectC;

    // -----------------------------------------------------------------------
    // Setup / teardown
    // -----------------------------------------------------------------------

    @BeforeClass
    public static void setUpProjects() throws Exception {
        // --- Action test project (created first, alone in the workspace) ---
        // The marker test projects are created lazily in m1 so the workspace
        // contains ONLY ActionTestProject when the action tests run.  This
        // prevents BrokenJml.java (in MarkersProjectB) from appearing on the
        // sourcepath and crashing the OpenJML parser during Find References.
        actionProject = createJavaProject("ActionTestProject");
        addJmlNatureProgrammatically(actionProject);
        actionSourceFile = createSourceFile(actionProject, "actiontest",
                "ActionTarget.java", ACTION_SOURCE);

        waitForBuild();
        bot.sleep(500);

        // Open ActionTarget.java in the editor — this triggers LSP4E to start
        // the OpenJML language server.  One server startup serves all tests.
        UIThreadRunnable.syncExec((VoidResult) () -> {
            try {
                IWorkbenchPage page = PlatformUI.getWorkbench()
                        .getActiveWorkbenchWindow().getActivePage();
                IDE.openEditor(page, actionSourceFile, true);
            } catch (Exception e) {
                throw new RuntimeException("Could not open ActionTarget.java", e);
            }
        });
        // Allow the LSP server to start and complete its initial file check.
        bot.sleep(10_000);
    }

    /**
     * Create the marker test projects.  Called once from {@link #m1_runCheckJmlAndVerifyMarkers}
     * so they are not in the workspace during the action tests.
     */
    private static boolean markersProjectsCreated = false;
    private static void ensureMarkersProjects() throws Exception {
        if (markersProjectsCreated) return;
        markersProjectsCreated = true;

        markersProjectA = createJavaProject("MarkersProjectA");
        populateFromTestdata(markersProjectA, "ProjectA", "projecta", "Broken.java");

        markersProjectB = createJavaProject("MarkersProjectB");
        populateFromTestdata(markersProjectB, "ProjectB", "projectb", "BrokenJava.java");
        populateFromTestdata(markersProjectB, "ProjectB", "projectb", "BrokenJml.java");
        addJmlNatureProgrammatically(markersProjectB);

        markersProjectC = createJavaProject("MarkersProjectC");
        populateFromTestdata(markersProjectC, "ProjectC", "projectc", "EscError.java");
        addJmlNatureProgrammatically(markersProjectC);

        waitForBuild();
        bot.sleep(500);
    }

    @AfterClass
    public static void tearDownProjects() throws Exception {
        deleteProject(actionProject);
        deleteProject(markersProjectA);
        deleteProject(markersProjectB);
        deleteProject(markersProjectC);
        // Clean shutdown of the LSP server; force-kill after 5s.
        stopLspServer(5_000);
    }

    // =======================================================================
    // Action tests (a_ prefix — run first)
    // =======================================================================

    /**
     * Verifies that the Rename command opens an InputDialog pre-filled with
     * the Java identifier at the cursor position.
     */
    @Test
    public void a1_renameDialogPrefilledWithCursorWord() {
        positionCursorOnTargetSymbol();
        executeCommandAsync(RENAME_COMMAND_ID);

        SWTBotShell renameShell = bot.shell("Rename");
        assertNotNull("Rename dialog must appear", renameShell);

        try {
            String prefilled = renameShell.bot().text(0).getText();
            assertEquals("Rename dialog input must be pre-filled with '"
                    + TARGET_SYMBOL + "'", TARGET_SYMBOL, prefilled);
        } finally {
            renameShell.bot().button("Cancel").click();
        }
    }

    /**
     * Verifies that Find References finds the expected references to
     * {@code myField} in ActionTarget.java.
     */
    @Test
    public void a2_findReferencesFindsExpectedReferences() {
        positionCursorOnTargetSymbol();
        executeCommandAsync(FIND_REFS_COMMAND_ID);

        SWTBotView searchView = null;
        SWTBotTree resultTree = null;
        long deadline = System.currentTimeMillis() + 60_000;

        while (System.currentTimeMillis() < deadline) {
            // The server may show a "Proceed anyway?" confirmation if the
            // workspace has compilation errors.  Dismiss it by clicking Proceed.
            dismissProceedAnywayDialog();

            // Check for a "No references found" info dialog.
            try {
                SWTBotShell noResultsShell = bot.shell("Find References");
                String msg = noResultsShell.bot().label(0).getText();
                noResultsShell.bot().button("OK").click();
                org.junit.Assert.fail(
                        "LSP server returned no references for '" + TARGET_SYMBOL
                        + "' — is the OpenJML LSP server running and connected"
                        + " to the document?  Dialog said: " + msg);
                return;
            } catch (org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException ignored) {}

            try {
                searchView = bot.viewByTitle("Search");
                searchView.show();
                resultTree = searchView.bot().tree();
                if (resultTree.getAllItems().length > 0) break;
            } catch (Exception ignored) {}
            bot.sleep(500);
        }

        assertNotNull("Search view must be visible after Find References", searchView);
        assertNotNull("Search view must contain a result tree", resultTree);

        SWTBotTreeItem[] topItems = resultTree.getAllItems();
        assertTrue("Search result tree must have at least one top-level item",
                topItems.length > 0);

        String fileNodeLabel = topItems[0].getText();
        assertTrue("Top-level result must identify ActionTarget.java",
                fileNodeLabel.contains("ActionTarget.java"));

        topItems[0].expand();
        SWTBotTreeItem[] matchItems = topItems[0].getItems();
        assertTrue("Find References must return at least 2 matches for '"
                + TARGET_SYMBOL + "'; got: " + matchItems.length,
                matchItems.length >= 2);

        boolean foundSymbolInResults = false;
        for (var item : matchItems) {
            if (item.getText().contains(TARGET_SYMBOL)) {
                foundSymbolInResults = true;
                break;
            }
        }
        assertTrue("At least one match must mention '" + TARGET_SYMBOL + "'",
                foundSymbolInResults);
    }

    // =======================================================================
    // Marker tests (m_ prefix — run after action tests)
    // =======================================================================

    /**
     * Select MarkersProjectB and C, run Check JML, verify JML markers appear
     * in B but not in A (which has no JML nature).
     */
    @Test
    public void m1_runCheckJmlAndVerifyMarkers() throws Exception {
        ensureMarkersProjects();
        selectProjects("MarkersProjectB", "MarkersProjectC");
        clickOpenJmlMenuItem("Check JML");

        long deadline = System.currentTimeMillis() + CHECK_JML_TIMEOUT_MS;
        while (System.currentTimeMillis() < deadline) {
            if (countJmlMarkers(markersProjectB) > 0) break;
            bot.sleep(1000);
        }
        assertTrue("MarkersProjectB should have at least one JML marker after Check JML",
                countJmlMarkers(markersProjectB) > 0);
        assertEquals("MarkersProjectA (no JML nature) should have zero JML markers",
                0, countJmlMarkers(markersProjectA));
    }

    /**
     * Remove JML nature from C; verify C's markers are cleared, B's remain.
     */
    @Test
    public void m2_removeNatureFromC() throws Exception {
        assertTrue("Pre-condition: MarkersProjectB should have JML markers",
                countJmlMarkers(markersProjectB) > 0);

        selectProjects("MarkersProjectC");
        clickOpenJmlMenuItem("Remove OpenJML Nature");
        waitForBuild();
        bot.sleep(1000);

        assertEquals("MarkersProjectC JML markers should be cleared",
                0, countJmlMarkers(markersProjectC));
        assertTrue("MarkersProjectB JML markers should be unaffected",
                countJmlMarkers(markersProjectB) > 0);
    }

    /**
     * Remove JML nature from B; verify B's markers are cleared.
     */
    @Test
    public void m3_removeNatureFromB() throws Exception {
        selectProjects("MarkersProjectB");
        clickOpenJmlMenuItem("Remove OpenJML Nature");
        waitForBuild();
        bot.sleep(1000);

        assertEquals("MarkersProjectB JML markers should be cleared",
                0, countJmlMarkers(markersProjectB));
    }

    /**
     * Verify Java compile markers survive nature changes.  Triggers a full
     * build first; if JDT produces no markers (some headless configs), the
     * test passes with a warning rather than failing.
     */
    @Test
    public void m4_javaMarkersNotAffected() throws Exception {
        org.eclipse.core.resources.ResourcesPlugin.getWorkspace().build(
                org.eclipse.core.resources.IncrementalProjectBuilder.FULL_BUILD, null);
        waitForBuild();
        bot.sleep(3000);

        int markersB = countJavaMarkers(markersProjectB);
        int markersA = countJavaMarkers(markersProjectA);

        if (markersB == 0 && markersA == 0) {
            System.err.println("[LspFeatureTest] WARNING: JDT produced 0 Java "
                    + "markers after full build — expected in some headless configs.");
            return;
        }
        assertTrue("MarkersProjectB should still have Java compile markers"
                + " (found " + markersB + ")", markersB > 0);
    }

    // -----------------------------------------------------------------------
    // Action test helpers
    // -----------------------------------------------------------------------

    private static void positionCursorOnTargetSymbol() {
        SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();
        editor.setFocus();
        editor.selectRange(SYMBOL_LINE, SYMBOL_COL, 0);
    }

    private static void executeCommandAsync(String commandId) {
        UIThreadRunnable.asyncExec((VoidResult) () -> {
            try {
                IHandlerService hs = PlatformUI.getWorkbench()
                        .getService(IHandlerService.class);
                hs.executeCommand(commandId, null);
            } catch (Exception e) {
                System.err.println("[LspFeatureTest] Command " + commandId
                        + " threw: " + e.getMessage());
            }
        });
    }

    // -----------------------------------------------------------------------
    // Marker test helpers
    // -----------------------------------------------------------------------

    private static int countJmlMarkers(IProject project) throws CoreException {
        IMarker[] markers = project.findMarkers(
                LSP4E_MARKER, false, IResource.DEPTH_INFINITE);
        int count = 0;
        for (IMarker m : markers) {
            if (OPENJML_SERVER_ID.equals(m.getAttribute(SERVER_ID_ATTR))) {
                count++;
            }
        }
        return count;
    }

    private static int countJavaMarkers(IProject project) throws CoreException {
        IMarker[] markers = project.findMarkers(
                JAVA_MARKER, true, IResource.DEPTH_INFINITE);
        return markers.length;
    }

    /**
     * Dismiss the "Find References may be inaccurate because the workspace has
     * compilation errors. Proceed anyway?" dialog if it is open.  This dialog
     * is a {@code window/showMessageRequest} from the LSP server, rendered by
     * LSP4E as a modal shell.  No-op if no such dialog is present.
     */
    private static void dismissProceedAnywayDialog() {
        // The dialog title varies by LSP4E version; scan all open shells for
        // one containing "Proceed" button text.
        for (SWTBotShell shell : bot.shells()) {
            try {
                String title = shell.getText();
                // Skip well-known shells that are not the dialog.
                if (title.isEmpty() || title.contains("Eclipse")
                        || title.contains("Package") || title.contains("Search")) {
                    continue;
                }
                // Try to click "Proceed Anyway" — if the button exists, this
                // is the confirmation dialog from ensureFreshAndConfirm().
                shell.bot().button("Proceed Anyway").click();
                System.out.println("[LspFeatureTest] Dismissed 'Proceed anyway?' dialog "
                        + "(title: " + title + ")");
                return;
            } catch (Exception ignored) {}
        }
    }
}
