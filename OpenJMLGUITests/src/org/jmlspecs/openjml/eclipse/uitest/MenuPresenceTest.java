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
        assertMenuItemPresent(openJml, "Check JML");
        assertMenuItemPresent(openJml, "Run ESC");
        assertMenuItemPresent(openJml, "Run ESC for Method Under Cursor");
        assertMenuItemPresent(openJml, "Compile RAC");
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
    @Test
    public void mainMenu_openJmlMenuPresent() {
        SWTBotMenu openJml = bot.menu("OpenJML");
        assertNotNull("OpenJML top-level menu should be present", openJml);
        assertMenuItemPresent(openJml, "Check JML in File");
        assertMenuItemPresent(openJml, "Run ESC on Current File");
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
        // Check JML button
        assertToolbarButtonPresent("Check JML");
        // Run ESC button
        assertToolbarButtonPresent("Run ESC on Current File");
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Asserts that a submenu item with the given label is reachable from
     * {@code parentMenu}.  SWTBot throws {@code WidgetNotFoundException} if
     * the item is absent; this helper wraps that in a more informative failure.
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
     * Asserts that a toolbar button with the given tooltip is visible in the
     * main toolbar.
     */
    private static void assertToolbarButtonPresent(String tooltip) {
        try {
            SWTBotToolbarButton btn = bot.toolbarButtonWithTooltip(tooltip);
            assertNotNull("Toolbar button '" + tooltip + "' should be present", btn);
        } catch (Exception e) {
            org.junit.Assert.fail("Expected toolbar button '" + tooltip
                    + "' was not found: " + e.getMessage());
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
