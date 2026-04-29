package org.jmlspecs.openjml.eclipse.uitest;

import static org.junit.Assert.*;

import java.util.Arrays;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable;
import org.eclipse.swtbot.swt.finder.results.Result;
import org.eclipse.swtbot.swt.finder.results.VoidResult;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

/**
 * SWTBot test that verifies file-type icons are correctly assigned to
 * {@code .java}, {@code .jml}, and unknown-extension ({@code .xyz}) files.
 *
 * <p>Three files are created in a Java project, opened in Eclipse editors,
 * and their editor-tab title images are compared:
 * <ul>
 *   <li>{@code IconSample.java} — opened in the JDT Java editor; expected to
 *       carry JDT's standard Java-file icon (class/source overlay).</li>
 *   <li>{@code IconSample.jml}  — opened in the Generic Editor via LSP4E;
 *       expected to carry the OpenJML custom JML icon, registered via the
 *       {@code org.eclipse.ui.genericeditor.icons} extension point for the
 *       {@code org.jmlspecs.openjml.jmlSource} content type.</li>
 *   <li>{@code IconSample.xyz}  — opened in a plain text/generic editor;
 *       expected to carry Eclipse's default unknown/text-file icon.</li>
 * </ul>
 *
 * <p>The primary assertions are that all three icons are pairwise different,
 * which catches regressions where the JML icon is not registered correctly
 * and the file falls back to a generic icon shared with .java or .xyz.
 */
public class FileIconTest extends GUITestBase {

    private static IProject project;
    private static IFile javaFile;
    private static IFile jmlFile;
    private static IFile xyzFile;

    // -----------------------------------------------------------------------
    // Setup / teardown
    // -----------------------------------------------------------------------

    @BeforeClass
    public static void setUpProjects() throws Exception {
        project = createJavaProject("FileIconTestProject");

        // .java — minimal compilable Java class
        javaFile = createSourceFile(project, "icontest", "IconSample.java",
                "package icontest;\npublic class IconSample {}\n");

        // .jml — JML specification fragment (Java-like text, .jml extension)
        jmlFile = createSourceFile(project, "icontest", "IconSample.jml",
                "package icontest;\n// JML specification\n"
                + "//@ public model instance boolean ok;\n");

        // .xyz — java-like text in an unrecognised extension
        xyzFile = createSourceFile(project, "icontest", "IconSample.xyz",
                "package icontest;\npublic class IconSampleXyz {}\n");

        waitForBuild();

        // Open all three files in editors so their title images are available.
        openInEditor(javaFile);
        openInEditor(jmlFile);
        openInEditor(xyzFile);
    }

    @AfterClass
    public static void tearDownProjects() throws Exception {
        bot.closeAllEditors();
        deleteProject(project);
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /** Every file type must have a non-null editor title icon. */
    @Test
    public void testAllIconsPresent() {
        assertNotNull(".java editor must have a title icon",
                titleImageOf("IconSample.java"));
        assertNotNull(".jml editor must have a title icon",
                titleImageOf("IconSample.jml"));
        assertNotNull(".xyz editor must have a title icon",
                titleImageOf("IconSample.xyz"));
    }

    /**
     * The .jml icon must differ from the standard Java icon.
     *
     * <p>Failure means either the JML content-type is not registered, or
     * the {@code org.eclipse.ui.genericeditor.icons} contribution in
     * {@code plugin.xml} does not reference the right content type.
     */
    @Test
    public void testJavaAndJmlIconsDiffer() {
        Image javaIcon = titleImageOf("IconSample.java");
        Image jmlIcon  = titleImageOf("IconSample.jml");
        assertNotNull(javaIcon);
        assertNotNull(jmlIcon);
        assertFalse(".java icon must differ from .jml icon",
                imagesHaveSameData(javaIcon, jmlIcon));
    }

    /**
     * The .jml icon must differ from the generic unknown-file icon.
     *
     * <p>Failure means the JML file fell back to a plain text/generic icon
     * instead of the custom OpenJML JML icon.
     */
    @Test
    public void testJmlAndXyzIconsDiffer() {
        Image jmlIcon = titleImageOf("IconSample.jml");
        Image xyzIcon = titleImageOf("IconSample.xyz");
        assertNotNull(jmlIcon);
        assertNotNull(xyzIcon);
        assertFalse(".jml icon must differ from .xyz (unknown-type) icon",
                imagesHaveSameData(jmlIcon, xyzIcon));
    }

    /**
     * The .java icon must differ from the generic unknown-file icon.
     * This is a sanity check for the icon-comparison infrastructure.
     */
    @Test
    public void testJavaAndXyzIconsDiffer() {
        Image javaIcon = titleImageOf("IconSample.java");
        Image xyzIcon  = titleImageOf("IconSample.xyz");
        assertNotNull(javaIcon);
        assertNotNull(xyzIcon);
        assertFalse(".java icon must differ from .xyz (unknown-type) icon",
                imagesHaveSameData(javaIcon, xyzIcon));
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Opens {@code file} in the workbench default editor on the UI thread
     * and waits briefly for the editor to initialise.
     */
    private static void openInEditor(IFile file) {
        UIThreadRunnable.syncExec((VoidResult) () -> {
            try {
                var page = PlatformUI.getWorkbench()
                        .getActiveWorkbenchWindow().getActivePage();
                IDE.openEditor(page, file);
            } catch (Exception e) {
                throw new RuntimeException(
                        "Failed to open editor for " + file.getName(), e);
            }
        });
        // Allow the editor (and its icon) to finish initialising.
        bot.sleep(500);
    }

    /**
     * Returns the title image of the editor whose part name matches
     * {@code filename}, or {@code null} if no such editor is open.
     *
     * <p>The part name for a file editor is the filename including extension
     * (e.g. {@code "IconSample.jml"}).
     */
    private static Image titleImageOf(String filename) {
        return UIThreadRunnable.syncExec(new Result<Image>() {
            @Override
            public Image run() {
                var page = PlatformUI.getWorkbench()
                        .getActiveWorkbenchWindow().getActivePage();
                for (IEditorReference ref : page.getEditorReferences()) {
                    if (filename.equals(ref.getPartName())) {
                        return ref.getTitleImage();
                    }
                }
                return null;
            }
        });
    }

    /**
     * Returns {@code true} if two images have identical dimensions and
     * pixel data.  Used to assert that distinct file types have distinct icons.
     */
    private static boolean imagesHaveSameData(Image a, Image b) {
        if (a == b) return true;
        if (a == null || b == null) return false;
        ImageData da = a.getImageData();
        ImageData db = b.getImageData();
        if (da.width != db.width || da.height != db.height) return false;
        return Arrays.equals(da.data, db.data);
    }
}
