package org.jmlspecs.openjml.eclipse.uitest;

import static org.junit.Assert.assertNotNull;

import org.eclipse.core.resources.IProject;
import org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable;
import org.eclipse.swtbot.swt.finder.results.VoidResult;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
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
        SWTBotMenu esc = openJml.menu("Static check (ESC)");
        assertMenuItemPresent(esc, "As Single Task");
        assertMenuItemPresent(esc, "Split by File");
        assertMenuItemPresent(esc, "Split by Method");
        assertMenuItemPresent(openJml, "Cancel ESC");
        assertMenuItemWithTooltip(openJml, "Compile RAC",
                "Compiles JML runtime checks for selected objects");
        SWTBotMenu clear = openJml.menu("Clear Markers");
        assertMenuItemPresent(clear, "All");
        assertMenuItemPresent(clear, "Selected Files");
        assertMenuItemPresent(openJml, "Index Project");
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
        assertMenuItemPresent(openJml, "Static check (ESC)");
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
     *
     * <p>On macOS, {@code bot.menu()} needs an active shell to locate the menu
     * bar.  We explicitly activate the workbench window's shell via the UI
     * thread to ensure it is active before querying the menu.
     */
    @Test
    public void mainMenu_openJmlMenuPresent() {
        activateWorkbench();

        SWTBotMenu openJml = mainMenu("OpenJML");
        assertMenuItemWithTooltip(openJml, "Check JML in File",
                "Type-checks JML in selected objects");
        SWTBotMenu esc = openJml.menu("Static check (ESC)");
        assertMenuItemPresent(esc, "As Single Task");
        assertMenuItemPresent(esc, "For Method Under Cursor");
        assertMenuItemPresent(openJml, "Clear and Reindex");
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
        activateWorkbench();

        assertToolbarButton("Type-checks JML in selected objects");
        assertToolbarButton("Performs JML static checks for selected objects");
        assertToolbarButton("Compiles JML runtime checks for selected objects");
    }

    /** The workbench window's shell (the active shell may be another one, e.g. on macOS). */
    private static org.eclipse.swt.widgets.Shell workbenchShell() {
        return UIThreadRunnable.syncExec(() -> {
            org.eclipse.ui.IWorkbenchWindow w = org.eclipse.ui.PlatformUI.getWorkbench().getActiveWorkbenchWindow();
            if (w == null && org.eclipse.ui.PlatformUI.getWorkbench().getWorkbenchWindowCount() > 0)
                w = org.eclipse.ui.PlatformUI.getWorkbench().getWorkbenchWindows()[0];
            return w == null ? null : w.getShell();
        });
    }

    /** A top-level menu of the workbench window's menu bar; fails listing the menus found. */
    private static SWTBotMenu mainMenu(String label) {
        org.eclipse.swt.widgets.Shell shell = workbenchShell();
        assertNotNull("no workbench window", shell);
        StringBuilder found = new StringBuilder();
        org.eclipse.swt.widgets.MenuItem item = UIThreadRunnable.syncExec(() -> {
            org.eclipse.swt.widgets.Menu bar = shell.getMenuBar();
            if (bar == null) return null;
            for (org.eclipse.swt.widgets.MenuItem mi : bar.getItems()) {
                String t = mi.getText().replace("&", "");
                found.append('[').append(t).append(']');
                if (t.equals(label)) return mi;
            }
            return null;
        });
        assertNotNull("Top-level menu '" + label + "' not in the menu bar: " + found, item);
        // The workbench fills menu-bar menus on SWT.Show, which nothing sends on macOS here.
        UIThreadRunnable.syncExec((VoidResult) () -> showMenuTree(item.getMenu()));
        return new SWTBotMenu(item);
    }

    private static void showMenuTree(org.eclipse.swt.widgets.Menu menu) {
        if (menu == null) return;
        menu.notifyListeners(org.eclipse.swt.SWT.Show, new org.eclipse.swt.widgets.Event());
        for (org.eclipse.swt.widgets.MenuItem mi : menu.getItems()) showMenuTree(mi.getMenu());
    }

    /**
     * Asserts that a tool item with the given tooltip is in one of the workbench window's
     * tool bars; fails listing the tooltips found.  (Tool items are found by walking the
     * window's controls: the trim is not reachable through the active shell on macOS.)
     */
    private static void assertToolbarButton(String tooltip) {
        org.eclipse.swt.widgets.Shell shell = workbenchShell();
        assertNotNull("no workbench window", shell);
        java.util.List<String> found = new java.util.ArrayList<>();
        UIThreadRunnable.syncExec((VoidResult) () -> collectToolTips(shell, found));
        org.junit.Assert.assertTrue("Toolbar button '" + tooltip + "' not found; tooltips: " + found,
                found.contains(tooltip));
    }

    private static void collectToolTips(org.eclipse.swt.widgets.Control c, java.util.List<String> out) {
        if (c instanceof org.eclipse.swt.widgets.ToolBar tb) {
            for (org.eclipse.swt.widgets.ToolItem ti : tb.getItems()) {
                if (ti.getToolTipText() != null) out.add(ti.getToolTipText());
            }
        }
        if (c instanceof org.eclipse.swt.widgets.Composite comp) {
            for (org.eclipse.swt.widgets.Control child : comp.getChildren()) collectToolTips(child, out);
        }
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
