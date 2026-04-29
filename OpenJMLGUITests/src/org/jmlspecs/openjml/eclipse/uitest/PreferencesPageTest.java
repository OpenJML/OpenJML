package org.jmlspecs.openjml.eclipse.uitest;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runners.MethodSorters;

/**
 * GUI tests that verify the OpenJML Preferences page can be opened and
 * contains the expected fields.
 *
 * <h3>What is tested</h3>
 * <ul>
 *   <li><b>Preferences page loads</b> — opening Window &gt; Preferences &gt;
 *       OpenJML must not throw a {@code ClassNotFoundException} or other error.
 *       This catches {@code Bundle-ClassPath} misconfigurations that prevent
 *       OSGi from finding the {@code OpenJMLPreferences} class.</li>
 *   <li><b>Key fields are present</b> — the preferences page must contain
 *       field editors for the LSP server path, check trigger, ESC trigger,
 *       and other settings defined in {@code OpenJMLOptions}.</li>
 * </ul>
 *
 * <h3>Note</h3>
 * No project is needed — the Preferences dialog is global to the workbench.
 * The dialog is closed with Cancel so no preferences are modified.
 */
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class PreferencesPageTest extends SwtBotTestBase {

    /**
     * Opens the Preferences dialog, navigates to the OpenJML page, and
     * verifies it loads without error.
     *
     * <p>This is the primary regression test for
     * <a href="https://github.com/OpenJML/OpenJML/issues/XXX">ClassNotFoundException:
     * OpenJMLPreferences</a>, which was caused by {@code Bundle-ClassPath: bin/}
     * in MANIFEST.MF placing classes at an incorrect location inside the plugin JAR.
     */
    @Test
    public void t1_preferencesPageLoadsWithoutError() {
        openPreferencesDialog();
        SWTBotShell prefsShell = bot.shell("Preferences");
        assertNotNull("Preferences dialog must be open", prefsShell);
        // Skip activate() — on headless macOS it times out even though
        // the shell is open.  Using prefsShell.bot() still works.

        try {
            // Navigate to OpenJML page in the left-hand tree.
            SWTBotTree tree = prefsShell.bot().tree();
            SWTBotTreeItem openJmlNode = tree.getTreeItem("OpenJML");
            assertNotNull("'OpenJML' node must exist in the Preferences tree", openJmlNode);
            openJmlNode.click();

            // If the class can't be loaded, Eclipse shows an error page instead
            // of the real preference page.  Detect this by checking for the
            // presence of at least one label that we know the real page creates.
            // The LSP Server section header is always the first thing on the page.
            bot.sleep(500);  // allow the page to render

            // Verify no error dialog appeared (OSGi class-loading failure
            // sometimes pops a separate error dialog).
            dismissErrorDialogIfPresent();

            // The page should contain the "Server script path" field label.
            // If the page failed to load, this label won't be found.
            boolean foundServerPathField = false;
            try {
                prefsShell.bot().textWithLabel(
                        "Server script path (blank = find on PATH or beside Eclipse):");
                foundServerPathField = true;
            } catch (Exception e) {
                // Try alternative: some FieldEditorPreferencePage layouts use
                // the label as a separate widget rather than part of the text widget.
                try {
                    prefsShell.bot().label(
                            "Server script path (blank = find on PATH or beside Eclipse):");
                    foundServerPathField = true;
                } catch (Exception ignored) {}
            }
            assertTrue(
                    "OpenJML Preferences page must contain the LSP server path field "
                    + "(if missing, the page class probably failed to load)",
                    foundServerPathField);
        } finally {
            closePreferencesDialog(prefsShell);
        }
    }

    /**
     * Verifies that key preference fields are present on the OpenJML page.
     * Currently only the LSP Server path field is shown; additional fields
     * may be re-enabled in the future.
     */
    @Test
    public void t2_preferencesPageContainsExpectedFields() {
        openPreferencesDialog();
        SWTBotShell prefsShell = bot.shell("Preferences");

        try {
            prefsShell.bot().tree().getTreeItem("OpenJML").click();
            bot.sleep(500);

            // The LSP Server section header must be present.
            assertLabelPresent(prefsShell, "LSP Server");
        } finally {
            closePreferencesDialog(prefsShell);
        }
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Opens the Preferences dialog using the Eclipse command framework.
     * Menu-based approaches fail on macOS where Preferences is in the native
     * application menu which SWTBot cannot access in headless mode.
     *
     * <p>Uses {@code asyncExec} because the Preferences dialog is modal — a
     * {@code syncExec} would deadlock (the dialog event loop blocks until
     * the dialog is closed, but SWTBot needs the main thread to interact
     * with it).
     */
    private static void openPreferencesDialog() {
        org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable.asyncExec(
                (org.eclipse.swtbot.swt.finder.results.VoidResult) () -> {
            try {
                org.eclipse.ui.handlers.IHandlerService hs =
                        org.eclipse.ui.PlatformUI.getWorkbench()
                                .getService(org.eclipse.ui.handlers.IHandlerService.class);
                hs.executeCommand("org.eclipse.ui.window.preferences", null);
            } catch (Exception e) {
                System.err.println("[PreferencesPageTest] Failed to open Preferences: " + e);
            }
        });
    }

    /**
     * Robustly close the Preferences dialog — try Cancel button first, then
     * shell.close() as a fallback.  No-op if the shell is already closed.
     */
    private static void closePreferencesDialog(SWTBotShell shell) {
        try {
            shell.bot().button("Cancel").click();
        } catch (Exception e) {
            try { shell.close(); } catch (Exception ignored) {}
        }
    }

    /**
     * Checks that a label with the given text exists in the shell.
     */
    private static void assertLabelPresent(SWTBotShell shell, String labelText) {
        try {
            shell.bot().label(labelText);
        } catch (Exception e) {
            org.junit.Assert.fail("Expected label '" + labelText
                    + "' not found on the Preferences page: " + e.getMessage());
        }
    }

    /**
     * Dismiss any error dialog that may have appeared (e.g. from a class-loading
     * failure).  No-op if no error dialog is open.
     */
    private static void dismissErrorDialogIfPresent() {
        for (String title : new String[]{"Error", "Problem Occurred",
                "Internal Error", "Unhandled event loop exception"}) {
            try {
                SWTBotShell errShell = bot.shell(title);
                errShell.bot().button("OK").click();
                org.junit.Assert.fail("An error dialog appeared with title '"
                        + title + "' — the Preferences page likely failed to load.");
            } catch (org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException ignored) {
                // Good: no error dialog
            }
        }
    }
}
