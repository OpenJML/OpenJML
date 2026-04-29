package org.jmlspecs.openjml.eclipse.uitest;

import static org.junit.Assert.*;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.junit.BeforeClass;
import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runners.MethodSorters;
import org.junit.runner.RunWith;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;

/**
 * SWTBot test that installs the OpenJML Eclipse plugin through the standard
 * Eclipse "Install New Software" wizard and then verifies the result via
 * "Help &gt; About … &gt; Installation Details".
 *
 * <p>This is the <em>initialization test</em>: it should be run before any
 * other GUI test class.  The Makefile {@code run-install-test} target copies
 * the pristine Eclipse (which has SWTBot but not OpenJML) to a test instance,
 * drops this bundle into its plugins directory, and then launches the
 * Eclipse PDE JUnit test runner against this class.
 *
 * <h3>Update site</h3>
 * The update site URL is passed via the system property
 * {@value #UPDATE_SITE_PROP}.  The Makefile sets this to the local
 * filesystem path of the sibling {@code openjml.github.io/eclipse-update-site}
 * directory (as a {@code file://} URL).  Override with
 * {@code -Dopenjml.update.site=<url>} for a published site.
 *
 * <h3>Platforms</h3>
 * Tested on macOS (the Eclipse binary handles {@code -XstartOnFirstThread}
 * automatically).  On Linux, the Makefile prepends {@code xvfb-run}.
 */
@RunWith(SWTBotJunit4ClassRunner.class)
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class InstallPluginTest extends SwtBotTestBase {

    /** System property: the p2 update site URL. Set by the Makefile launcher. */
    public static final String UPDATE_SITE_PROP = "openjml.update.site";

    /** IU name: the OpenJML feature group. Used in log messages. */
    private static final String OPENJML_LABEL = "OpenJML";

    private static String updateSiteUrl;

    @BeforeClass
    public static void setUpInstallTest() {
        SwtBotTestBase.baseSetUp();
        updateSiteUrl = System.getProperty(UPDATE_SITE_PROP);
        assertNotNull(
            "System property '" + UPDATE_SITE_PROP + "' must be set. " +
            "Run via the Makefile: make run-install-test",
            updateSiteUrl);
        System.out.println("[InstallPluginTest] update site: " + updateSiteUrl);
    }

    // -----------------------------------------------------------------------
    // Tests (run in name order: t1 → t2)
    // -----------------------------------------------------------------------

    /**
     * Drive the Eclipse "Install New Software" wizard to install OpenJML
     * from the configured update site.
     */
    @Test
    public void t1_installOpenJmlViaWizard() {
        // Open the "Install New Software" wizard via the Eclipse command
        // framework (asyncExec) instead of bot.menu("Help"), which requires
        // an active shell and fails on macOS headless SWTBot runs.
        org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable.asyncExec(
                (org.eclipse.swtbot.swt.finder.results.VoidResult) () -> {
            try {
                org.eclipse.ui.handlers.IHandlerService hs =
                        org.eclipse.ui.PlatformUI.getWorkbench()
                                .getService(org.eclipse.ui.handlers.IHandlerService.class);
                hs.executeCommand("org.eclipse.equinox.p2.ui.sdk.install", null);
            } catch (Exception e) {
                System.err.println("[InstallPluginTest] Failed to open install wizard: " + e);
            }
        });

        // Scope all subsequent wizard interactions to the Install shell so that
        // button/tree lookups are not confused by other open shells or dialogs.
        SWTBotShell installShell = bot.shell("Install");
        // SWTBot's activate() waits for the OS to report the shell as active, which
        // times out on macOS when another app has focus.  forceActive()+setFocus()
        // is stronger and does not block waiting for OS confirmation.
        org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable.syncExec(
                (org.eclipse.swtbot.swt.finder.results.VoidResult) () -> {
            installShell.widget.forceActive();
            installShell.widget.setFocus();
        });
        bot.sleep(300);
        System.out.println("[InstallPluginTest] Install dialog open");

        // --- Enter update site URL in the "Work with:" combo ---
        // Type the URL but do NOT press Enter yet — uncheck "Group items by category"
        // first so the tree populates with the raw feature list rather than category
        // headings.  The OpenJML p2 metadata does not include category IUs, so with
        // grouping enabled the tree shows "There are no categorized items" and nothing
        // is selectable.  Disabling grouping before the load avoids a two-step wait.
        installShell.bot().comboBoxWithLabel("Work with:").setText(updateSiteUrl);

        // Uncheck "Group items by category" before triggering the repository load.
        try {
            installShell.bot().checkBox("Group items by category").deselect();
            System.out.println("[InstallPluginTest] Unchecked 'Group items by category'");
        } catch (WidgetNotFoundException e) {
            System.out.println("[InstallPluginTest] 'Group items by category' not found; continuing");
        }

        // Now press Enter to trigger the repository load.
        installShell.bot().comboBoxWithLabel("Work with:")
                          .pressShortcut(org.eclipse.swt.SWT.CR, (char) 0);

        // --- Wait for the feature tree to populate (up to 90 s for file:// or network) ---
        System.out.println("[InstallPluginTest] Waiting for feature list...");
        bot.waitUntil(Conditions.treeHasRows(installShell.bot().tree(), 1), 90_000);
        System.out.println("[InstallPluginTest] Feature list loaded");

        // --- Check all items via direct SWT events so p2's SelectionListener fires.
        //
        // SWTBot's "Select All" button click triggers the button widget, but in
        // Eclipse 2026-03 the p2 install wizard's CheckboxTreeViewer listener does
        // not reliably fire in response to the button event.  Directly calling
        // setChecked(true) + notifyListeners(SWT.Selection, CHECK) on each tree item
        // guarantees the AvailableIUsPage listener receives the check-state-changed
        // notification and triggers dependency resolution.
        org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable.syncExec(
                (org.eclipse.swtbot.swt.finder.results.VoidResult) () -> {
            org.eclipse.swt.widgets.Tree tree = installShell.bot().tree().widget;
            System.out.println("[InstallPluginTest] Tree has "
                    + tree.getItemCount() + " top-level item(s)");
            for (org.eclipse.swt.widgets.TreeItem item : tree.getItems()) {
                System.out.println("[InstallPluginTest]   Checking: '" + item.getText()
                        + "' (was checked=" + item.getChecked() + ")");
                item.setChecked(true);
                // Fire the SWT.Selection/SWT.CHECK event that p2's viewer listener
                // requires in order to start dependency resolution.
                org.eclipse.swt.widgets.Event ev = new org.eclipse.swt.widgets.Event();
                ev.type   = org.eclipse.swt.SWT.Selection;
                ev.detail = org.eclipse.swt.SWT.CHECK;
                ev.widget = tree;
                ev.item   = item;
                tree.notifyListeners(org.eclipse.swt.SWT.Selection, ev);
            }
        });

        // --- Wait for p2 to finish dependency resolution, dismissing any
        //     blocking dialogs (Trust, unsigned-content warnings) that may
        //     appear before or during resolution in newer Eclipse versions.
        //     "Next >" enables once p2 reports no errors.
        //     All lookups are scoped to installShell to avoid false positives.
        System.out.println("[InstallPluginTest] Waiting for dependency resolution...");
        waitForNextButtonDismissingBlockers(installShell, 90_000);
        System.out.println("[InstallPluginTest] Dependency resolution complete; clicking Next >");
        installShell.bot().button("Next >").click();

        // The "Install Details" page now computes sizes; wait for Next > again.
        waitForNextButtonDismissingBlockers(installShell, 60_000);

        // --- Next: "Review Licenses" page (if present) ---
        try {
            installShell.bot().button("Next >").click();
        } catch (WidgetNotFoundException e) {
            // Some wizard configurations skip directly to Finish
            System.out.println("[InstallPluginTest] No third Next > page; proceeding to Finish");
        }

        // --- Accept license (may or may not appear depending on the feature) ---
        try {
            installShell.bot().radio("I accept the terms of the license agreements").click();
        } catch (WidgetNotFoundException e) {
            // No license page — some features omit it
            System.out.println("[InstallPluginTest] No license page; continuing");
        }

        // --- Finish: kick off the actual download+install ---
        System.out.println("[InstallPluginTest] Clicking Finish...");
        bot.button("Finish").click();

        // --- Wait for install to complete (up to 120 s) ---
        // The "Install" shell closes when done; then a restart prompt may appear.
        bot.waitWhile(Conditions.shellIsActive("Install"), 120_000);
        System.out.println("[InstallPluginTest] Install shell closed");

        // Handle unsigned-content warning if it appears
        try {
            SWTBotShell warning = bot.shell("Trust");
            warning.activate();
            // Click "Trust Selected" or "Select All" then "Trust Selected"
            try { bot.button("Select All").click(); } catch (WidgetNotFoundException ignored) {}
            bot.button("Trust Selected").click();
            bot.waitWhile(Conditions.shellIsActive("Trust"), 15_000);
        } catch (WidgetNotFoundException ignored) {}

        // --- Dismiss the restart prompt with "Restart Later" ---
        // We verify installation in the same JVM session (via the profile).
        try {
            SWTBotShell restartShell = bot.shell("Software Updates");
            restartShell.activate();
            System.out.println("[InstallPluginTest] Restart dialog: choosing 'Restart Later'");
            bot.button("Restart Later").click();
        } catch (WidgetNotFoundException e) {
            System.out.println("[InstallPluginTest] No restart dialog");
        }

        System.out.println("[InstallPluginTest] Installation complete");
    }

    /**
     * Verify that OpenJML appears in "Help &gt; About … &gt; Installation Details
     * &gt; Installed Software".  This reads from the p2 profile so it does not
     * require a restart to reflect the just-installed feature.
     */
    @Test
    public void t2_verifyOpenJmlInInstalledSoftware() {
        activateWorkbench();

        // --- Help > About Eclipse IDE ---
        bot.menu("Help").menu("About Eclipse").click();

        SWTBotShell aboutShell = findShell("About Eclipse IDE", "About Eclipse");
        aboutShell.activate();

        // --- Click "Installation Details" button ---
        bot.button("Installation Details").click();

        SWTBotShell detailsShell = findShell(
                "Eclipse IDE Installation Details", "Installation Details");
        detailsShell.activate();

        // --- Switch to "Installed Software" tab ---
        bot.tabItem("Installed Software").activate();

        // Wait a moment for the table to populate
        bot.sleep(2_000);

        // --- Search the table for "OpenJML" ---
        SWTBotTable table = bot.table();
        boolean found = false;
        int rows = table.rowCount();
        System.out.println("[InstallPluginTest] Installed Software rows: " + rows);
        for (int i = 0; i < rows; i++) {
            String text = table.getTableItem(i).getText(0);
            if (text != null && text.contains(OPENJML_LABEL)) {
                System.out.println("[InstallPluginTest] Found: " + text);
                found = true;
                break;
            }
        }

        // Close before asserting to leave the workbench in a clean state
        bot.button("Close").click();

        assertTrue(
            "OpenJML feature should appear in Installed Software after installation",
            found);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Polls until the "Next >" button in the active Install shell is enabled,
     * dismissing any blocking dialogs (Trust, unsigned-content warnings) that
     * may appear in newer Eclipse versions while p2 resolves requirements.
     * Throws {@link AssertionError} if the button is still not enabled after
     * {@code timeoutMs} milliseconds.
     */
    private static void waitForNextButtonDismissingBlockers(
            SWTBotShell installShell, long timeoutMs) {
        long deadline = System.currentTimeMillis() + timeoutMs;
        int iteration = 0;
        while (System.currentTimeMillis() < deadline) {
            iteration++;
            // Dismiss any trust / unsigned-content shell that appeared.
            // These pop up over the Install shell so they are not children of it;
            // scan all open shells but only dismiss known blocker titles.
            for (SWTBotShell shell : bot.shells()) {
                String title = shell.getText();
                if (title.equals("Trust") || title.equals("Unsigned Content")
                        || title.equals("Security Warning")) {
                    System.out.println(
                            "[InstallPluginTest] Dismissing dialog: " + title);
                    try { shell.bot().button("Select All").click(); }
                    catch (WidgetNotFoundException ignored) {}
                    try { shell.bot().button("Trust Selected").click(); }
                    catch (WidgetNotFoundException e) {
                        try { shell.bot().button("OK").click(); }
                        catch (WidgetNotFoundException ignored) {}
                    }
                }
            }
            // Check if Next > is now enabled — scoped to the Install shell.
            // On first attempt and periodically, log button/label state for diagnosis.
            try {
                boolean enabled = installShell.bot().button("Next >").isEnabled();
                if (iteration == 1 || iteration % 20 == 0) {
                    System.out.println("[InstallPluginTest] 'Next >' found, enabled=" + enabled
                            + " (iteration " + iteration + ")");
                }
                if (enabled) return;
            } catch (WidgetNotFoundException e) {
                if (iteration <= 3 || iteration % 20 == 0) {
                    System.out.println("[InstallPluginTest] 'Next >' not found (iteration "
                            + iteration + "): " + e.getMessage());
                    // On first few misses, dump available button labels for diagnosis.
                    dumpButtonsInShell(installShell);
                }
            }
            bot.sleep(500);
        }
        org.junit.Assert.fail(
                "Timed out (" + timeoutMs + "ms) waiting for 'Next >' to become enabled"
                + " during p2 dependency resolution");
    }

    /**
     * Prints all Button widget texts found anywhere within {@code shell} to
     * stdout.  Called on diagnosis when "Next >" is not found.
     */
    private static void dumpButtonsInShell(SWTBotShell shell) {
        org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable.syncExec(
                (org.eclipse.swtbot.swt.finder.results.VoidResult) () ->
                    dumpButtons(shell.widget, 0));
    }

    private static void dumpButtons(org.eclipse.swt.widgets.Composite parent, int depth) {
        String indent = "  ".repeat(depth);
        for (org.eclipse.swt.widgets.Control child : parent.getChildren()) {
            if (child instanceof org.eclipse.swt.widgets.Button) {
                org.eclipse.swt.widgets.Button b = (org.eclipse.swt.widgets.Button) child;
                System.out.println("[InstallPluginTest] " + indent
                        + "Button: '" + b.getText()
                        + "' enabled=" + b.isEnabled()
                        + " visible=" + b.isVisible());
            }
            if (child instanceof org.eclipse.swt.widgets.Composite) {
                dumpButtons((org.eclipse.swt.widgets.Composite) child, depth + 1);
            }
        }
    }

    /**
     * Try each title in order; return the first shell found.
     * Accommodates minor variations in the "About" dialog title across releases.
     */
    private static SWTBotShell findShell(String... titles) {
        WidgetNotFoundException last = null;
        for (String title : titles) {
            try {
                return bot.shell(title);
            } catch (WidgetNotFoundException e) {
                last = e;
            }
        }
        throw last;
    }
}
