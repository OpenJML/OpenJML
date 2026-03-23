package org.jmlspecs.openjml.eclipse.uitest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
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
 * GUI tests that verify OpenJML actions correctly extract command arguments
 * from the active editor's selection.
 *
 * <h3>What is tested</h3>
 * <ul>
 *   <li><b>Rename dialog pre-fill</b> — triggering the OpenJML Rename command
 *       ({@code org.openjml.eclipse.commands.rename}) when the cursor sits on
 *       a Java identifier opens an {@link org.eclipse.jface.dialogs.InputDialog}
 *       whose input text is pre-populated with that exact identifier.
 *       This verifies {@code JmlRenameHandler.getWordAtOffset()} correctly
 *       extracts the cursor word and passes it to the dialog.</li>
 *   <li><b>Find References produces correct results</b> — triggering the OpenJML
 *       Find References command ({@code org.openjml.eclipse.commands.findReferences})
 *       populates the Eclipse Search view with at least the two expected references
 *       to {@code myField} (the Java field declaration and the JML {@code requires}
 *       clause) in {@code ActionTarget.java}.  This verifies that
 *       {@code JmlFindReferencesHandler} builds valid {@code ReferenceParams},
 *       the LSP server returns the correct locations, and they are correctly
 *       mapped to {@code LocatedMatch} entries visible in the Search tree.</li>
 * </ul>
 *
 * <h3>Test setup</h3>
 * One Java project ({@code ActionTestProject}) is created with JML nature.
 * A single source file {@code ActionTarget.java} is used for all tests.
 * Tests are ordered alphabetically (t1_, t2_, …) because they share project state.
 *
 * <h3>Limitations</h3>
 * These tests do NOT assert that the LSP server returns correct references or
 * that the rename edit is accurate — those correctness properties are covered by
 * the unit tests in {@code OpenJMLTest/lsp/} (e.g. {@code RenameTest1/2/3},
 * {@code ReferenceFinderTest}).  The goal here is to verify the Eclipse-side
 * wiring: that the correct command is triggered and that the cursor word is
 * correctly extracted as a command argument.
 */
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class ActionTest extends GUITestBase {

    /** Command ID for the OpenJML Rename handler (from plugin.xml). */
    private static final String RENAME_COMMAND_ID =
            "org.openjml.eclipse.commands.rename";

    /** Command ID for the OpenJML Find References handler (from plugin.xml). */
    private static final String FIND_REFS_COMMAND_ID =
            "org.openjml.eclipse.commands.findReferences";

    /** Identifier we position the cursor on in every test. */
    private static final String TARGET_SYMBOL = "myField";

    /** The test project and source file reused by all tests. */
    private static IProject project;
    private static IFile    sourceFile;

    /**
     * Source file content.  {@code myField} appears twice:
     * once as a Java field declaration (line 1) and once in a JML {@code requires}
     * clause (line 2).  Line/column numbers are 0-indexed.
     *
     * <pre>
     * line 0: package actiontest;
     * line 1: public class ActionTarget {
     * line 2:     public int myField = 0;          ← myField at col 15
     * line 3:     //@ requires myField >= 0;
     * line 4:     public void method(int x) { }
     * line 5: }
     * </pre>
     */
    private static final String SOURCE =
            "package actiontest;\n"
            + "public class ActionTarget {\n"
            + "    public int myField = 0;\n"
            + "    //@ requires myField >= 0;\n"
            + "    public void method(int x) { }\n"
            + "}\n";

    // line index (0-based) and column of TARGET_SYMBOL in the declaration
    // line 0: package actiontest;
    // line 1: public class ActionTarget {
    // line 2:     public int myField = 0;   ← myField at col 15
    private static final int SYMBOL_LINE = 2;
    private static final int SYMBOL_COL  = 15;   // "    public int " = 15 chars

    // -----------------------------------------------------------------------
    // Setup / teardown
    // -----------------------------------------------------------------------

    @BeforeClass
    public static void setUpProjects() throws Exception {
        project = createJavaProject("ActionTestProject");
        addJmlNatureProgrammatically(project);
        sourceFile = createSourceFile(project, "actiontest", "ActionTarget.java", SOURCE);
        waitForBuild();
        bot.sleep(500);

        // Open the file in the editor so it is available for the tests.
        // LSP4E starts the server when the first Java file is opened; give it
        // time to launch and complete its initial file check before t2 runs.
        UIThreadRunnable.syncExec((VoidResult) () -> {
            try {
                IWorkbenchPage page = PlatformUI.getWorkbench()
                        .getActiveWorkbenchWindow().getActivePage();
                IDE.openEditor(page, sourceFile, true);
            } catch (Exception e) {
                throw new RuntimeException("Could not open ActionTarget.java", e);
            }
        });
        bot.sleep(5_000);  // allow LSP server startup + initial file check
    }

    @AfterClass
    public static void tearDownProjects() throws Exception {
        deleteProject(project);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Positions the editor cursor at {@link #SYMBOL_LINE} / {@link #SYMBOL_COL}
     * so that {@code getWordAtOffset} in the handlers will extract
     * {@link #TARGET_SYMBOL}.
     */
    private static void positionCursorOnTargetSymbol() {
        SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();
        editor.setFocus();
        // selectRange(line, column, length=0) places the cursor without making
        // a text selection, which is exactly what the handlers expect.
        editor.selectRange(SYMBOL_LINE, SYMBOL_COL, 0);
    }

    /**
     * Execute an Eclipse command asynchronously on the UI thread, so that
     * the SWTBot main thread can then wait for a shell or view to appear.
     * {@code syncExec} would deadlock for commands that open modal dialogs.
     */
    private static void executeCommandAsync(String commandId) {
        UIThreadRunnable.asyncExec((VoidResult) () -> {
            try {
                IHandlerService hs = PlatformUI.getWorkbench()
                        .getService(IHandlerService.class);
                hs.executeCommand(commandId, null);
            } catch (Exception e) {
                // Log but don't fail here — assertion in the calling test
                System.err.println("[ActionTest] Command " + commandId
                        + " threw: " + e.getMessage());
            }
        });
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /**
     * Verifies that the Rename command opens an {@code InputDialog} whose input
     * text is pre-filled with the Java identifier at the cursor position.
     *
     * <p>This exercises {@code JmlRenameHandler.getWordAtOffset()}: if that
     * method fails to extract the cursor word correctly, the pre-fill text
     * would be wrong (empty or a different substring).
     *
     * <p>The dialog is cancelled at the end so no LSP call is made and the
     * file is not modified.
     */
    @Test
    public void t1_renameDialogPrefilledWithCursorWord() {
        positionCursorOnTargetSymbol();

        // Execute the Rename command asynchronously; the handler opens a
        // modal InputDialog on the UI thread which would block syncExec.
        executeCommandAsync(RENAME_COMMAND_ID);

        // SWTBot waits (up to SWTBotPreferences.TIMEOUT ms) for the shell.
        SWTBotShell renameShell = bot.shell("Rename");
        assertNotNull("Rename dialog must appear after command execution", renameShell);
        // Skip activate() — on headless macOS it times out even though
        // the shell is open.  Using renameShell.bot() still works.

        try {
            // The dialog title text shows "New name for '<currentName>':" as
            // the label; the input field contains the pre-filled current name.
            String prefilled = renameShell.bot().text(0).getText();
            assertEquals(
                    "Rename dialog input must be pre-filled with the cursor word '"
                            + TARGET_SYMBOL + "'",
                    TARGET_SYMBOL, prefilled);
        } finally {
            // Always cancel so the test leaves no side effects.
            renameShell.bot().button("Cancel").click();
        }
    }

    /**
     * Verifies that the Find References command finds the expected references to
     * {@link #TARGET_SYMBOL} ({@code myField}) in {@code ActionTarget.java}.
     *
     * <p>The source file contains exactly two uses of {@code myField}: the Java
     * field declaration on line 1 and a JML {@code requires} clause on line 2.
     * Both must appear in the Search view's result tree after the query completes.
     *
     * <p>This test validates the full pipeline:
     * <ol>
     *   <li>{@code JmlFindReferencesHandler} extracts the cursor word and builds
     *       a {@code ReferenceParams} pointing at the correct document and position.</li>
     *   <li>The LSP server calls {@code ReferenceFinder.findReferences} and returns
     *       locations for both the Java and JML occurrences.</li>
     *   <li>{@code JmlReferencesSearchQuery} converts the LSP locations to
     *       {@code LocatedMatch} entries and populates the Search view.</li>
     * </ol>
     *
     * <p><b>Requires the OpenJML LSP server to be running</b> in the test Eclipse.
     * If the server is not available the handler shows a "No references found"
     * info dialog and this test fails with a message explaining the requirement.
     */
    @Test
    public void t2_findReferencesFindsExpectedReferences() {
        positionCursorOnTargetSymbol();
        executeCommandAsync(FIND_REFS_COMMAND_ID);

        // The query is async; wait up to 35s for either results or a "no results"
        // dialog (the latter is shown when the LSP server returns an empty list,
        // e.g. when it is not running or not connected to the document).
        SWTBotView searchView = null;
        SWTBotTree resultTree = null;
        long deadline = System.currentTimeMillis() + 35_000;

        while (System.currentTimeMillis() < deadline) {
            // If the handler showed a "No references found" dialog, the LSP server
            // did not return results.  Fail with an actionable message.
            try {
                SWTBotShell noResultsShell = bot.shell("Find References");
                String msg = noResultsShell.bot().label(0).getText();
                noResultsShell.bot().button("OK").click();
                org.junit.Assert.fail(
                        "LSP server returned no references for '" + TARGET_SYMBOL
                        + "' — is the OpenJML LSP server running and connected"
                        + " to the document?  Dialog said: " + msg);
                return;
            } catch (org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException ignored) {
                // Good: no "no results" dialog yet
            }

            // Check if the Search view has populated with results.
            try {
                searchView = bot.viewByTitle("Search");
                searchView.show();
                resultTree = searchView.bot().tree();
                if (resultTree.getAllItems().length > 0) break;
            } catch (Exception ignored) {
                // Search view not yet visible
            }
            bot.sleep(500);
        }

        assertNotNull("Search view must be visible after Find References", searchView);
        assertNotNull("Search view must contain a result tree", resultTree);

        // The test file has myField in 2 places: the Java declaration and the JML
        // requires clause.  The top-level tree item is the file node; its label
        // reports the file name and match count (e.g. "ActionTarget.java — 2 references").
        SWTBotTreeItem[] topItems = resultTree.getAllItems();
        assertTrue("Search result tree must have at least one top-level item",
                topItems.length > 0);

        String fileNodeLabel = topItems[0].getText();
        assertTrue("Top-level search result must identify the source file 'ActionTarget.java'",
                fileNodeLabel.contains("ActionTarget.java"));

        // Expand the file node to reveal individual match rows.
        topItems[0].expand();
        SWTBotTreeItem[] matchItems = topItems[0].getItems();
        assertTrue(
                "Find References must return at least 2 matches for '" + TARGET_SYMBOL
                + "' (Java declaration + JML requires clause); got: " + matchItems.length,
                matchItems.length >= 2);

        // Each match row is labelled "N: source-line-text".  At least one must
        // mention myField so we know the cursor word was correctly passed to the
        // server as the subject of the search.
        boolean foundSymbolInResults = false;
        for (var item : matchItems) {
            if (item.getText().contains(TARGET_SYMBOL)) {
                foundSymbolInResults = true;
                break;
            }
        }
        assertTrue("At least one match row must mention '" + TARGET_SYMBOL + "'",
                foundSymbolInResults);
    }
}
