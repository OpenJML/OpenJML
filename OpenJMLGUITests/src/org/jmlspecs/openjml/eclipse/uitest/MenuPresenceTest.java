package org.jmlspecs.openjml.eclipse.uitest;

import static org.junit.Assert.assertNotNull;

import org.eclipse.core.resources.IProject;
import org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable;
import org.eclipse.swtbot.swt.finder.results.VoidResult;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotToolbarButton;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

/**
 * GUI tests that verify the presence of OpenJML menu items and toolbar buttons.
 *
 * <h3>What is tested</h3>
 * <ul>
 *   <li>The "OpenJML" submenu appears in the Package Explorer context menu
 *       when a Java project is selected, and contains all expected items.</li>
 *   <li>The "OpenJML" top-level menu is present in the main menu bar and
 *       contains all expected items.</li>
 *   <li>OpenJML toolbar buttons are present in the main toolbar.</li>
 * </ul>
 *
 * <p>These tests do not click any action items — they only verify that the
 * menu/toolbar wiring in {@code plugin.xml} is correct and that items are
 * visible when a Java project is selected.
 *
 * <p>A single plain Java project (no JML nature) is sufficient for most checks.
 * A second project with JML nature is created to verify items whose visibility
 * depends on the nature (e.g. "Remove OpenJML Nature").
 */
public class MenuPresenceTest extends GUITestBase {

    private static IProject plainProject;
    private static IProject jmlProject;

    // -----------------------------------------------------------------------
    // Setup / teardown
    // -----------------------------------------------------------------------

    @BeforeClass
    public static void setUpProjects() throws Exception {
        plainProject = createJavaProject("MenuTestPlainProject");
        populateFromTestdata(plainProject, "ProjectA", "projecta", "Broken.java");

        jmlProject = createJavaProject("MenuTestJmlProject");
        populateFromTestdata(jmlProject, "ProjectB", "projectb", "BrokenJml.java");
        addJmlNatureProgrammatically(jmlProject);

        waitForBuild();
        bot.sleep(500);
    }

    @AfterClass
    public static void tearDownProjects() throws Exception {
        deleteProject(plainProject);
        deleteProject(jmlProject);
    }

    // -----------------------------------------------------------------------
    // Context-menu items (Package Explorer right-click)
    // -----------------------------------------------------------------------

    /**
     * Verifies that the "OpenJML" submenu is present in the Package Explorer
     * context menu when a plain Java project (no JML nature) is selected,
     * and that all expected items are reachable within it.
     */
    @Test
    public void contextMenu_allItemsPresentForPlainProject() {
        selectProjects("MenuTestPlainProject");
        SWTBotMenu openJml = packageExplorerTree().contextMenu("OpenJML");
        assertMenuItemWithTooltip(openJml, "Check JML",
                "Type-checks JML in selected objects");
        assertMenuItemWithTooltip(openJml, "Run ESC",
                "Performs JML static checks for selected objects");
        assertMenuItemPresent(openJml, "Run ESC for Method Under Cursor");
        assertMenuItemWithTooltip(openJml, "Compile RAC",
                "Compiles JML runtime checks for selected objects");
        assertMenuItemPresent(openJml, "Clear Markers");
        assertMenuItemPresent(openJml, "Clear and Reindex");
        assertMenuItemPresent(openJml, "Add OpenJML Nature");
        assertMenuItemPresent(openJml, "Remove OpenJML Nature");
        closeOpenMenu();
    }

    /**
     * Verifies that the "OpenJML" submenu is present when a JML-natured
     * project is selected (the menu must not disappear after nature is added).
     */
    @Test
    public void contextMenu_allItemsPresentForJmlProject() {
        selectProjects("MenuTestJmlProject");
        SWTBotMenu openJml = packageExplorerTree().contextMenu("OpenJML");
        assertMenuItemPresent(openJml, "Check JML");
        assertMenuItemPresent(openJml, "Run ESC");
        assertMenuItemPresent(openJml, "Add OpenJML Nature");
        assertMenuItemPresent(openJml, "Remove OpenJML Nature");
        closeOpenMenu();
    }

    // -----------------------------------------------------------------------
    // Main menu bar (Window menu → OpenJML)
    // -----------------------------------------------------------------------

    /**
     * Verifies that the "OpenJML" top-level menu appears in the Eclipse menu
     * bar and contains the key action items.
     */
    /**
     * Verifies that the "OpenJML" top-level menu appears in the Eclipse menu
     * bar and contains the key action items.
     *
     * <p>On macOS, {@code bot.menu()} needs an active shell to locate the menu
     * bar.  We explicitly activate the workbench window's shell via the UI
     * thread to ensure it is active before querying the menu.
     */
    @Test
    public void mainMenu_openJmlMenuPresent() {
        // Force the workbench shell to become the active shell.
        UIThreadRunnable.syncExec((VoidResult) () -> {
            org.eclipse.swt.widgets.Shell wbShell =
                    org.eclipse.ui.PlatformUI.getWorkbench()
                            .getActiveWorkbenchWindow().getShell();
            wbShell.forceActive();
            wbShell.setFocus();
        });
        bot.sleep(200);

        SWTBotMenu openJml = bot.menu("OpenJML");
        assertNotNull("OpenJML top-level menu should be present", openJml);
        assertMenuItemWithTooltip(openJml, "Check JML in File",
                "Type-checks JML in selected objects");
        assertMenuItemWithTooltip(openJml, "Run ESC on Current File",
                "Performs JML static checks for selected objects");
        assertMenuItemPresent(openJml, "Add OpenJML Nature");
        assertMenuItemPresent(openJml, "Remove OpenJML Nature");
        closeOpenMenu();
    }

    // -----------------------------------------------------------------------
    // Toolbar buttons
    // -----------------------------------------------------------------------

    /**
     * Verifies that the OpenJML toolbar contains the expected action buttons.
     *
     * <p>Toolbar button presence is checked by tooltip text, which is the
     * most stable identifier across Eclipse versions.
     */
    @Test
    public void toolbar_openJmlButtonsPresent() {
        // Ensure the workbench shell is active so SWTBot can find toolbar items.
        UIThreadRunnable.syncExec((VoidResult) () -> {
            org.eclipse.swt.widgets.Shell wbShell =
                    org.eclipse.ui.PlatformUI.getWorkbench()
                            .getActiveWorkbenchWindow().getShell();
            wbShell.forceActive();
            wbShell.setFocus();
        });
        bot.sleep(200);

        assertIconToolbarButton("Type-checks JML in selected objects");
        assertToolbarButton("ESC", "Performs JML static checks for selected objects");
        assertToolbarButton("RAC", "Compiles JML runtime checks for selected objects");
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Asserts that a submenu item with the given label is reachable from
     * {@code parentMenu}.
     */
    private static void assertMenuItemPresent(SWTBotMenu parentMenu, String label) {
        try {
            assertNotNull("Menu item '" + label + "' should be present",
                    parentMenu.menu(label));
        } catch (Exception e) {
            org.junit.Assert.fail("Expected menu item '" + label
                    + "' was not found: " + e.getMessage());
        }
    }

    /**
     * Asserts that a submenu item is present and carries the expected tooltip text.
     */
    private static void assertMenuItemWithTooltip(SWTBotMenu parentMenu,
                                                   String label, String expectedTooltip) {
        try {
            SWTBotMenu item = parentMenu.menu(label);
            assertNotNull("Menu item '" + label + "' should be present", item);
            org.junit.Assert.assertEquals(
                    "Tooltip for menu item '" + label + "'",
                    expectedTooltip, item.getToolTipText());
        } catch (Exception e) {
            org.junit.Assert.fail("Menu item '" + label + "': " + e.getMessage());
        }
    }

    /**
     * Asserts that an icon-only toolbar button with the given tooltip exists and
     * that its tooltip text matches.  Icon buttons have no visible text label so
     * SWTBot must locate them by tooltip.
     */
    private static void assertIconToolbarButton(String tooltip) {
        try {
            SWTBotToolbarButton btn = bot.toolbarButtonWithTooltip(tooltip);
            assertNotNull("Icon toolbar button '" + tooltip + "' should be present", btn);
            org.junit.Assert.assertEquals(
                    "Tooltip text mismatch", tooltip, btn.getToolTipText());
        } catch (Exception e) {
            org.junit.Assert.fail("Icon toolbar button '" + tooltip
                    + "' not found: " + e.getMessage());
        }
    }

    /**
     * Asserts that a text-label toolbar button with the given label exists and
     * that its tooltip text matches.  Text buttons have no icon, so SWTBot can
     * locate them by their visible label.
     */
    private static void assertToolbarButton(String label, String expectedTooltip) {
        try {
            SWTBotToolbarButton btn = bot.toolbarButton(label);
            assertNotNull("Toolbar button '" + label + "' should be present", btn);
            org.junit.Assert.assertEquals(
                    "Tooltip for toolbar button '" + label + "'",
                    expectedTooltip, btn.getToolTipText());
        } catch (Exception e) {
            org.junit.Assert.fail("Toolbar button '" + label
                    + "' not found: " + e.getMessage());
        }
    }

    /**
     * Closes any open menu by firing an Escape key event on the active shell.
     * Called at the end of tests that open menus without clicking an item.
     */
    private static void closeOpenMenu() {
        UIThreadRunnable.syncExec((VoidResult) () -> {
            org.eclipse.swt.widgets.Display d =
                    org.eclipse.swt.widgets.Display.getDefault();
            org.eclipse.swt.widgets.Event e = new org.eclipse.swt.widgets.Event();
            e.keyCode = org.eclipse.swt.SWT.ESC;
            e.type = org.eclipse.swt.SWT.KeyDown;
            org.eclipse.swt.widgets.Shell active = d.getActiveShell();
            if (active != null) active.notifyListeners(org.eclipse.swt.SWT.KeyDown, e);
        });
        bot.sleep(100);
    }
}
