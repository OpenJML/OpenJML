package org.jmlspecs.openjml.eclipse.uitest;

import java.io.ByteArrayInputStream;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable;
import org.eclipse.swtbot.swt.finder.results.VoidResult;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.AfterClass;
import org.junit.BeforeClass;

/**
 * Base class for OpenJMLUI SWTBot tests that manipulate Eclipse projects.
 *
 * <p>Provides helpers for:
 * <ul>
 *   <li>Creating Java projects programmatically (for test setup)</li>
 *   <li>Populating projects with source files from testdata/</li>
 *   <li>Adding/removing JML nature programmatically or via GUI menu</li>
 *   <li>Selecting items in the Package Explorer</li>
 *   <li>Interacting with the Problems view</li>
 *   <li>Waiting for Eclipse builders/jobs to finish</li>
 * </ul>
 *
 * <p>Subclasses should call {@link #setUpProjects()} from their own
 * {@code @BeforeClass} to create the projects they need, and
 * {@link #tearDownProjects()} from {@code @AfterClass} to clean up.
 */
public abstract class GUITestBase extends SwtBotTestBase {

    /** OpenJML nature identifier (matches plugin.xml). */
    protected static final String JML_NATURE_ID = "org.openjml.OpenJMLUI.JMLNatureID";

    /** JRE container path string — avoids a compile-time dependency on jdt.launching. */
    private static final String JRE_CONTAINER =
            "org.eclipse.jdt.launching.JRE_CONTAINER";

    // -----------------------------------------------------------------------
    // Lifecycle stubs — subclasses override
    // -----------------------------------------------------------------------

    @BeforeClass
    public static void setUpProjects() throws Exception {
        // Subclasses override to create test projects
    }

    @AfterClass
    public static void tearDownProjects() throws Exception {
        // Subclasses override to delete test projects
    }

    // -----------------------------------------------------------------------
    // Project creation / population
    // -----------------------------------------------------------------------

    /**
     * Creates a Java project in the current workspace with a {@code src/} source
     * folder and the default JRE container on its classpath.
     * If a project with this name already exists it is deleted first.
     */
    protected static IProject createJavaProject(String name) throws CoreException {
        IWorkspace ws = ResourcesPlugin.getWorkspace();
        IProject project = ws.getRoot().getProject(name);
        if (project.exists()) {
            project.delete(true, true, null);
        }

        IProjectDescription desc = ws.newProjectDescription(name);
        desc.setNatureIds(new String[] { JavaCore.NATURE_ID });
        project.create(desc, null);
        project.open(null);

        // Configure source folder and output
        IFolder srcFolder = project.getFolder("src");
        srcFolder.create(true, true, null);
        IFolder binFolder = project.getFolder("bin");
        binFolder.create(true, true, null);

        IJavaProject jp = JavaCore.create(project);
        jp.setOutputLocation(binFolder.getFullPath(), null);

        IClasspathEntry[] cp = new IClasspathEntry[] {
            JavaCore.newSourceEntry(srcFolder.getFullPath()),
            JavaCore.newContainerEntry(new Path(JRE_CONTAINER))
        };
        jp.setRawClasspath(cp, null);

        return project;
    }

    /**
     * Creates (or overwrites) a source file at
     * {@code <project>/src/<packageName>/<fileName>}.
     */
    protected static IFile createSourceFile(IProject project,
            String packageName, String fileName, String content) throws CoreException {
        IFolder src = project.getFolder("src");
        IFolder pkg = src.getFolder(packageName);
        if (!pkg.exists()) {
            pkg.create(false, true, null);
        }
        IFile file = pkg.getFile(fileName);
        byte[] bytes = content.getBytes(StandardCharsets.UTF_8);
        ByteArrayInputStream in = new ByteArrayInputStream(bytes);
        if (file.exists()) {
            file.setContents(in, true, false, null);
        } else {
            file.create(in, false, null);
        }
        return file;
    }

    /**
     * Reads a testdata source file and creates it in the given project.
     * The file is read from {@code testdata/projects/<testdataProject>/src/<pkg>/<name>}
     * inside this test bundle.
     *
     * <p>Note: since the test bundle packages {@code testdata/} as a directory inside
     * the jar, files are accessible via {@link Class#getResourceAsStream}.
     */
    protected static IFile populateFromTestdata(IProject project,
            String testdataProject, String packageName, String fileName) throws Exception {
        String resource = "/testdata/projects/" + testdataProject
                + "/src/" + packageName + "/" + fileName;
        try (java.io.InputStream is =
                GUITestBase.class.getResourceAsStream(resource)) {
            if (is == null) {
                throw new IllegalArgumentException(
                        "Testdata resource not found: " + resource);
            }
            String content = new String(is.readAllBytes(), StandardCharsets.UTF_8);
            return createSourceFile(project, packageName, fileName, content);
        }
    }

    /**
     * Deletes an Eclipse project (including its contents on disk).
     * No-op if the project does not exist.
     */
    protected static void deleteProject(IProject project) {
        if (project != null && project.exists()) {
            try {
                project.delete(true, true, null);
            } catch (CoreException e) {
                // best-effort cleanup — log and continue
                System.err.println("Warning: could not delete project "
                        + project.getName() + ": " + e.getMessage());
            }
        }
    }

    // -----------------------------------------------------------------------
    // JML nature helpers
    // -----------------------------------------------------------------------

    /** Returns {@code true} if the project has JML nature. */
    protected static boolean hasJmlNature(IProject project) throws CoreException {
        return project.isOpen() && project.hasNature(JML_NATURE_ID);
    }

    /**
     * Adds JML nature to a project programmatically (for test setup,
     * bypasses the GUI menu).
     */
    protected static void addJmlNatureProgrammatically(IProject project)
            throws CoreException {
        IProjectDescription desc = project.getDescription();
        String[] natures = desc.getNatureIds();
        if (!Arrays.asList(natures).contains(JML_NATURE_ID)) {
            String[] newNatures = Arrays.copyOf(natures, natures.length + 1);
            newNatures[natures.length] = JML_NATURE_ID;
            desc.setNatureIds(newNatures);
            project.setDescription(desc, null);
        }
    }

    /**
     * Removes JML nature from a project programmatically (for test setup,
     * bypasses the GUI menu).
     */
    protected static void removeJmlNatureProgrammatically(IProject project)
            throws CoreException {
        IProjectDescription desc = project.getDescription();
        String[] natures = desc.getNatureIds();
        String[] filtered = Arrays.stream(natures)
                .filter(n -> !JML_NATURE_ID.equals(n))
                .toArray(String[]::new);
        if (filtered.length != natures.length) {
            desc.setNatureIds(filtered);
            project.setDescription(desc, null);
        }
    }

    // -----------------------------------------------------------------------
    // Package Explorer helpers
    // -----------------------------------------------------------------------

    /**
     * Returns the Package Explorer view's tree widget, opening the view first
     * if it is not visible.
     */
    protected static SWTBotTree packageExplorerTree() {
        SWTBotView view;
        try {
            view = bot.viewByTitle("Package Explorer");
        } catch (Exception e) {
            // View might not be open — show it
            bot.menu("Window").menu("Show View").menu("Package Explorer").click();
            view = bot.viewByTitle("Package Explorer");
        }
        view.show();
        return view.bot().tree();
    }

    /**
     * Selects one or more top-level project nodes in the Package Explorer.
     * Uses SWTBot's built-in multi-select for top-level items.
     */
    protected static void selectProjects(String... projectNames) {
        SWTBotTree tree = packageExplorerTree();
        tree.select(projectNames);
    }

    /**
     * Selects {@code projectName} and {@code fileName} (under
     * {@code src/packageName/} in {@code fileProjectName}) simultaneously in
     * the Package Explorer.  This tests the behaviour where a file selection
     * triggers nature application on its containing project.
     *
     * <p>Uses a low-level SWT selection because SWTBot's API only supports
     * single-level multi-select natively.
     */
    protected static void selectProjectAndFileInOtherProject(
            String projectName,
            String fileProjectName, String packageName, String fileName) {
        SWTBotTree tree = packageExplorerTree();

        // Expand down to the target file
        SWTBotTreeItem projItem = tree.getTreeItem(fileProjectName);
        SWTBotTreeItem srcItem = projItem.expand().getNode("src");
        SWTBotTreeItem pkgItem = srcItem.expand().getNode(packageName);
        SWTBotTreeItem fileItem = pkgItem.expand().getNode(fileName);

        SWTBotTreeItem selectedProjectItem = tree.getTreeItem(projectName);

        // Set multi-selection via SWT (SWTBot has no public mixed-level API)
        multiSelectItems(selectedProjectItem, fileItem);
    }

    /**
     * Sets an arbitrary multi-selection across tree items at any nesting level.
     * Fires a {@code SWT.Selection} event so Eclipse's selection listeners update.
     */
    protected static void multiSelectItems(SWTBotTreeItem... items) {
        UIThreadRunnable.syncExec((VoidResult) () -> {
            if (items.length == 0) return;
            Tree swtTree = items[0].widget.getParent();
            TreeItem[] widgets = Arrays.stream(items)
                    .map(i -> i.widget)
                    .toArray(TreeItem[]::new);
            swtTree.setSelection(widgets);
            Event e = new Event();
            e.widget = swtTree;
            e.type = SWT.Selection;
            swtTree.notifyListeners(SWT.Selection, e);
        });
    }

    /**
     * Opens the OpenJML context menu on the current Package Explorer selection
     * and clicks the item with the given label.
     *
     * <p>Calls {@code tree.contextMenu("OpenJML").menu(label).click()}.
     * This works correctly after multi-select because {@code SWTBotTree.contextMenu}
     * does not reset the selection (unlike {@code SWTBotTreeItem.contextMenu}).
     */
    protected static void clickOpenJmlMenuItem(String label) {
        SWTBotTree tree = packageExplorerTree();
        tree.contextMenu("OpenJML").menu(label).click();
    }

    /**
     * Convenience: select the given top-level projects, then click an OpenJML
     * context-menu item.
     */
    protected static void selectProjectsAndRunOpenJml(String label,
            String... projectNames) {
        selectProjects(projectNames);
        clickOpenJmlMenuItem(label);
    }

    // -----------------------------------------------------------------------
    // Builder / job synchronisation
    // -----------------------------------------------------------------------

    /**
     * Waits for all Eclipse auto-build and pending UI jobs to complete.
     * Call this after triggering an action that modifies project configuration
     * (e.g. adding/removing a nature) so that assertions see the final state.
     */
    protected static void waitForBuild() {
        // Join the auto-build job family
        try {
            org.eclipse.core.runtime.jobs.IJobManager jobs =
                    org.eclipse.core.runtime.jobs.Job.getJobManager();
            jobs.join(ResourcesPlugin.FAMILY_AUTO_BUILD, null);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
        // Drain pending UI events
        UIThreadRunnable.syncExec((VoidResult) () -> {
            while (org.eclipse.swt.widgets.Display.getCurrent().readAndDispatch()) {
                // drain
            }
        });
    }

    // -----------------------------------------------------------------------
    // Problems view helpers
    // -----------------------------------------------------------------------

    /**
     * Opens the Problems view (if not already open) and returns it.
     */
    protected static SWTBotView openProblemsView() {
        try {
            return bot.viewByTitle("Problems");
        } catch (Exception e) {
            // Not open — show it
            bot.menu("Window").menu("Show View").menu("Other...").click();
            bot.shell("Show View").bot().tree()
                    .expandNode("General").select("Problems");
            bot.shell("Show View").bot().button("Open").click();
            return bot.viewByTitle("Problems");
        }
    }

    /**
     * Returns the number of items in the Problems view whose description text
     * contains {@code fragment} (case-sensitive substring match).
     */
    protected static int countProblemsContaining(String fragment) {
        SWTBotView view = openProblemsView();
        SWTBotTree tree = view.bot().tree();
        int count = 0;
        for (SWTBotTreeItem category : tree.getAllItems()) {
            try {
                for (SWTBotTreeItem item : category.expand().getItems()) {
                    if (item.getText().contains(fragment)) {
                        count++;
                    }
                }
            } catch (Exception ignored) {}
        }
        return count;
    }

    /**
     * Returns the total number of items under all top-level categories in the
     * Problems view whose resource column value matches {@code projectName}.
     */
    protected static int countProblemsInProject(String projectName) {
        SWTBotView view = openProblemsView();
        SWTBotTree tree = view.bot().tree();
        int count = 0;
        for (SWTBotTreeItem category : tree.getAllItems()) {
            try {
                for (SWTBotTreeItem item : category.expand().getItems()) {
                    // Check each visible column for the project name.
                    // Column indices vary by Eclipse version; scan 0–4.
                    boolean found = false;
                    for (int col = 0; col < 5 && !found; col++) {
                        try {
                            if (item.cell(col).contains(projectName)) {
                                found = true;
                            }
                        } catch (Exception ignored) {}
                    }
                    if (found) count++;
                }
            } catch (Exception ignored) {}
        }
        return count;
    }

    // -----------------------------------------------------------------------
    // Project Properties — nature check
    // -----------------------------------------------------------------------

    /**
     * Opens the Project Properties dialog for {@code projectName}, navigates to
     * the "Project Natures" page, and returns {@code true} if any nature entry
     * in the table contains {@code expectedNatureLabel} (case-insensitive substring).
     *
     * <p>The dialog is closed with Cancel so no changes are committed.
     * The "Project Natures" property page is contributed by the PDE/IDE layer
     * and lists each nature by its {@code name} attribute from {@code plugin.xml}.
     * For OpenJML the label is {@code "OpenJML Nature"}.
     */
    protected static boolean hasNatureInProperties(String projectName,
            String expectedNatureLabel) {
        selectProjects(projectName);
        // Open properties via the context menu on the Package Explorer tree.
        // Using tree.contextMenu("Properties") preserves the multi-selection
        // (unlike SWTBotTreeItem.contextMenu which re-selects a single item).
        // bot.menu("Project").menu("Properties") is unreliable in headless
        // SWTBot runs because the menu item is only populated when the view
        // has keyboard focus, which is not guaranteed.
        SWTBotTree tree = packageExplorerTree();
        tree.contextMenu("Properties").click();
        org.eclipse.swtbot.swt.finder.widgets.SWTBotShell shell =
                bot.shell("Properties for " + projectName);
        shell.activate();
        try {
            // Navigate to "Project Natures" in the left navigation tree.
            // The page is a top-level node contributed by org.eclipse.pde.ui.
            org.eclipse.swtbot.swt.finder.widgets.SWTBotTree nav =
                    shell.bot().tree();
            nav.getTreeItem("Project Natures").click();

            // The page content is a checkbox table listing registered natures.
            // Check each row's text for the expected label.
            org.eclipse.swtbot.swt.finder.widgets.SWTBotTable table =
                    shell.bot().table();
            for (int row = 0; row < table.rowCount(); row++) {
                String cellText = table.cell(row, 0);
                if (cellText.toLowerCase().contains(
                        expectedNatureLabel.toLowerCase())) {
                    return true;
                }
            }
            return false;
        } finally {
            shell.bot().button("Cancel").click();
        }
    }

    // -----------------------------------------------------------------------
    // -----------------------------------------------------------------------
    // Console view helpers
    // -----------------------------------------------------------------------

    /**
     * Returns the text currently visible in the Console view, or an empty
     * string if the Console is not open / has no content.
     */
    protected static String getConsoleText() {
        try {
            SWTBotView console = bot.viewByTitle("Console");
            console.show();
            return console.bot().styledText().getText();
        } catch (Exception e) {
            return "";
        }
    }
}
