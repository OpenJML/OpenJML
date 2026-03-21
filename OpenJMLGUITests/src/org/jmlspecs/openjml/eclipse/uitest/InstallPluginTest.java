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
        // --- Open the Install New Software dialog ---
        bot.menu("Help").menu("Install New Software...").click();

        SWTBotShell installShell = bot.shell("Install");
        installShell.activate();
        System.out.println("[InstallPluginTest] Install dialog open");

        // --- Enter update site URL in the "Work with:" combo ---
        // Type the URL and press Enter to trigger the repository load.
        bot.comboBoxWithLabel("Work with:").setText(updateSiteUrl);
        bot.comboBoxWithLabel("Work with:")
           .pressShortcut(org.eclipse.swt.SWT.CR, (char) 0);

        // --- Wait for the feature tree to populate (up to 90 s for file:// or network) ---
        System.out.println("[InstallPluginTest] Waiting for feature list...");
        bot.waitUntil(Conditions.treeHasRows(bot.tree(), 1), 90_000);
        System.out.println("[InstallPluginTest] Feature list loaded");

        // --- Select all items (OpenJML is the only feature in the site) ---
        bot.button("Select All").click();

        // --- Next: "Install Details" page ---
        bot.button("Next >").click();
        // Wait for the "Next >" button to become enabled again (details computed)
        bot.waitUntil(Conditions.widgetIsEnabled(bot.button("Next >")), 30_000);

        // --- Next: "Review Licenses" page ---
        bot.button("Next >").click();

        // --- Accept license (may or may not appear depending on the feature) ---
        try {
            bot.radio("I accept the terms of the license agreements").click();
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
        // --- Help > About Eclipse IDE ---
        bot.menu("Help").menu("About Eclipse IDE").click();

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
