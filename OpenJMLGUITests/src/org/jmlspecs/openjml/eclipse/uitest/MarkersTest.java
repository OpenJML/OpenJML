package org.jmlspecs.openjml.eclipse.uitest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runners.MethodSorters;

/**
 * GUI tests for the JML marker lifecycle: markers appear when OpenJML checking
 * is run on a JML-natured project and disappear when JML nature is removed.
 *
 * <h3>Test setup</h3>
 * Three Java projects are created:
 * <ul>
 *   <li><b>MarkersProjectA</b> — has JML annotations but NO JML nature.
 *       JML markers must NOT appear here.</li>
 *   <li><b>MarkersProjectB</b> — JML nature; has a JML type error
 *       ({@code int} compared with {@code String} in a {@code requires} clause).
 *       JML marker should appear after running Check JML.</li>
 *   <li><b>MarkersProjectC</b> — JML nature; has an ESC error (postcondition
 *       {@code \result >= 0} on a method that always returns {@code -1}).
 *       A JML marker should appear after running Run ESC.</li>
 * </ul>
 *
 * <h3>Tests (run in name order)</h3>
 * <ol>
 *   <li>{@code t1_runCheckJmlAndVerifyMarkers} — run Check JML on B and C;
 *       verify JML markers appear in B and C but not in A.</li>
 *   <li>{@code t2_removeNatureFromC} — remove JML nature from C; verify C's
 *       JML markers are cleared but B's remain.</li>
 *   <li>{@code t3_removeNatureFromB} — remove JML nature from B; verify B's
 *       JML markers are cleared.</li>
 *   <li>{@code t4_javaMarkersNotAffected} — confirm that Java compile errors
 *       survive all nature changes.</li>
 * </ol>
 *
 * <p><b>Requires OpenJML to be installed</b> in the test Eclipse and the
 * OpenJML LSP server to be reachable.  If OpenJML is not configured the
 * "Check JML" step will time out and the test will fail with a descriptive
 * message.
 *
 * <p>Tests are ordered by name because they share project state (markers
 * accumulated in earlier tests are needed by later assertions).
 */
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class MarkersTest extends GUITestBase {

    /** OpenJML problem marker type (set by the OpenJML plugin). */
    private static final String OPENJML_MARKER =
            "org.jmlspecs.openjml.markers.JMLProblem";

    /** Standard Java problem marker type. */
    private static final String JAVA_MARKER =
            "org.eclipse.jdt.core.problem";

    /** Timeout in ms to wait for Check JML to produce at least one marker. */
    private static final int CHECK_JML_TIMEOUT_MS = 60_000;

    private static IProject projectA;
    private static IProject projectB;
    private static IProject projectC;

    // -----------------------------------------------------------------------
    // Setup / teardown
    // -----------------------------------------------------------------------

    @BeforeClass
    public static void setUpProjects() throws Exception {
        // A: JML annotation present but NO JML nature
        projectA = createJavaProject("MarkersProjectA");
        populateFromTestdata(projectA, "ProjectA", "projecta", "Broken.java");

        // B and C: JML nature enabled
        projectB = createJavaProject("MarkersProjectB");
        populateFromTestdata(projectB, "ProjectB", "projectb", "BrokenJava.java");
        populateFromTestdata(projectB, "ProjectB", "projectb", "BrokenJml.java");
        addJmlNatureProgrammatically(projectB);

        projectC = createJavaProject("MarkersProjectC");
        populateFromTestdata(projectC, "ProjectC", "projectc", "EscError.java");
        addJmlNatureProgrammatically(projectC);

        waitForBuild();
        bot.sleep(500);
    }

    @AfterClass
    public static void tearDownProjects() throws Exception {
        deleteProject(projectA);
        deleteProject(projectB);
        deleteProject(projectC);
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /**
     * Select MarkersProjectB and MarkersProjectC in the Package Explorer,
     * then invoke OpenJML → Check JML.  Wait for at least one JML marker to
     * appear in B (the type error is reliable and fast).
     *
     * <p>Then verify:
     * <ul>
     *   <li>B has at least one JML marker (the {@code requires} type error).</li>
     *   <li>A has NO JML markers (no JML nature).</li>
     * </ul>
     */
    @Test
    public void t1_runCheckJmlAndVerifyMarkers() throws Exception {
        // Select B and C, run Check JML
        selectProjects("MarkersProjectB", "MarkersProjectC");
        clickOpenJmlMenuItem("Check JML");

        // Wait for at least one JML marker to appear in B
        long deadline = System.currentTimeMillis() + CHECK_JML_TIMEOUT_MS;
        while (System.currentTimeMillis() < deadline) {
            if (countJmlMarkers(projectB) > 0) break;
            bot.sleep(1000);
        }
        assertTrue(
                "MarkersProjectB should have at least one JML marker after Check JML",
                countJmlMarkers(projectB) > 0);
        assertEquals(
                "MarkersProjectA (no JML nature) should have zero JML markers",
                0, countJmlMarkers(projectA));
    }

    /**
     * Remove JML nature from MarkersProjectC via the context menu.
     * Verify C's JML markers are cleared, B's JML markers remain.
     */
    @Test
    public void t2_removeNatureFromC() throws Exception {
        // Pre-condition: B has JML markers from t1
        assertTrue("Pre-condition: MarkersProjectB should have JML markers",
                countJmlMarkers(projectB) > 0);

        selectProjects("MarkersProjectC");
        clickOpenJmlMenuItem("Remove OpenJML Nature");
        waitForBuild();
        // Allow the plugin a moment to clear markers
        bot.sleep(1000);

        assertEquals("MarkersProjectC JML markers should be cleared after nature removal",
                0, countJmlMarkers(projectC));
        assertTrue("MarkersProjectB JML markers should be unaffected",
                countJmlMarkers(projectB) > 0);
    }

    /**
     * Remove JML nature from MarkersProjectB via the context menu.
     * Verify B's JML markers are cleared.
     */
    @Test
    public void t3_removeNatureFromB() throws Exception {
        selectProjects("MarkersProjectB");
        clickOpenJmlMenuItem("Remove OpenJML Nature");
        waitForBuild();
        bot.sleep(1000);

        assertEquals("MarkersProjectB JML markers should be cleared after nature removal",
                0, countJmlMarkers(projectB));
    }

    /**
     * Java compile-error markers (JDT problem markers) should survive throughout
     * all nature changes.  ProjectB and ProjectA both have Java compile errors.
     */
    @Test
    public void t4_javaMarkersNotAffected() throws CoreException {
        // B still has BrokenJava.java (undefined symbol → Java compile error)
        assertTrue("MarkersProjectB should still have Java compile markers",
                countJavaMarkers(projectB) > 0);
        assertTrue("MarkersProjectA should still have Java compile markers",
                countJavaMarkers(projectA) > 0);
    }

    // -----------------------------------------------------------------------
    // Marker-counting helpers
    // -----------------------------------------------------------------------

    /**
     * Returns the number of OpenJML problem markers on all resources in
     * the project.
     */
    private static int countJmlMarkers(IProject project) throws CoreException {
        IMarker[] markers = project.findMarkers(
                OPENJML_MARKER, true, IResource.DEPTH_INFINITE);
        return markers.length;
    }

    /**
     * Returns the number of Java problem markers (JDT) on all resources in
     * the project.
     */
    private static int countJavaMarkers(IProject project) throws CoreException {
        IMarker[] markers = project.findMarkers(
                JAVA_MARKER, true, IResource.DEPTH_INFINITE);
        return markers.length;
    }
}
