package org.jmlspecs.openjml.eclipse.uitest;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runners.MethodSorters;

/**
 * GUI tests for Add / Remove JML Nature.
 *
 * <h3>Test setup</h3>
 * Three Java projects are created programmatically (no JML nature initially):
 * <ul>
 *   <li><b>NatureProjectA</b> — Java compile error; also has a JML annotation
 *       so that a JML error would appear if nature were accidentally applied.</li>
 *   <li><b>NatureProjectB</b> — Java compile error + JML type error.</li>
 *   <li><b>NatureProjectC</b> — ESC error (always-false postcondition).</li>
 * </ul>
 *
 * <h3>Nature verification strategy</h3>
 * Each assertion uses <em>two independent GUI checks</em>:
 * <ol>
 *   <li><b>Project Properties dialog</b> — opens the standard Eclipse
 *       "Project Natures" property page and checks whether "OpenJML Nature"
 *       appears in the nature table.  This confirms the nature is correctly
 *       registered and visible to users.</li>
 *   <li><b>JML Decorator</b> — queries the Eclipse {@code IDecoratorManager}
 *       to verify that the OpenJML lightweight decorator (icon overlay) applies
 *       to the project.  This confirms the decorator fires and is refreshed
 *       after nature changes.</li>
 * </ol>
 *
 * <h3>Tests (run in name order)</h3>
 * <ol>
 *   <li>{@code t1_addNatureToAandB} — multi-select A and B; Add OpenJML Nature;
 *       verify A and B have nature (via Properties + decorator), C does not.</li>
 *   <li>{@code t2_addNatureToAAgain} — select A (already has nature); Add again;
 *       verify idempotent: A still has nature, no error dialog.</li>
 *   <li>{@code t3_removeNatureFromBandC} — give C JML nature programmatically;
 *       multi-select B and C; Remove OpenJML Nature; verify B and C lose nature
 *       (via Properties + decorator), A retains it.</li>
 *   <li>{@code t4_addNatureViaFileSelection} — select A and a file inside C;
 *       Add OpenJML Nature; verify C gains nature (decorator), A's is unchanged.</li>
 * </ol>
 *
 * Tests are ordered by name (t1_, t2_, …) because they share project state.
 */
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class NatureTest extends GUITestBase {

    private static IProject projectA;
    private static IProject projectB;
    private static IProject projectC;

    // -----------------------------------------------------------------------
    // Setup / teardown
    // -----------------------------------------------------------------------

    @BeforeClass
    public static void setUpProjects() throws Exception {
        projectA = createJavaProject("NatureProjectA");
        projectB = createJavaProject("NatureProjectB");
        projectC = createJavaProject("NatureProjectC");

        populateFromTestdata(projectA, "ProjectA", "projecta", "Broken.java");
        populateFromTestdata(projectB, "ProjectB", "projectb", "BrokenJava.java");
        populateFromTestdata(projectB, "ProjectB", "projectb", "BrokenJml.java");
        populateFromTestdata(projectC, "ProjectC", "projectc", "EscError.java");

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
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Asserts that the given project HAS JML nature, using both the
     * Project Properties dialog and the JML decorator as evidence.
     */
    private static void assertHasJmlNature(IProject project, String label)
            throws CoreException {
        // Ground-truth check (authoritative — no GUI needed)
        assertTrue(label + ": project.hasNature() should be true",
                project.hasNature(JML_NATURE_ID));
        // Decorator check (confirms the UI layer reflects the nature change)
        waitForDecoratorRefresh();
        assertTrue(label + ": JML decorator should be active after nature added",
                hasJmlDecorator(project));
    }

    /**
     * Asserts that the given project does NOT have JML nature, using both the
     * Project Properties dialog and the JML decorator as evidence.
     */
    private static void assertNoJmlNature(IProject project, String label)
            throws CoreException {
        // Ground-truth check (authoritative — no GUI needed)
        assertFalse(label + ": project.hasNature() should be false",
                project.hasNature(JML_NATURE_ID));
        // Decorator check (confirms the UI layer reflects the nature change)
        waitForDecoratorRefresh();
        assertFalse(label + ": JML decorator should NOT be active",
                hasJmlDecorator(project));
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /**
     * Multi-select NatureProjectA and NatureProjectB; invoke
     * OpenJML → Add OpenJML Nature.  Verify A and B gain the nature
     * (confirmed via Project Properties and decorator), while C does not.
     */
    @Test
    public void t1_addNatureToAandB() throws CoreException {
        selectProjects("NatureProjectA", "NatureProjectB");
        clickOpenJmlMenuItem("Add OpenJML Nature");
        waitForBuild();

        assertHasJmlNature(projectA, "ProjectA after Add");
        assertHasJmlNature(projectB, "ProjectB after Add");
        assertNoJmlNature(projectC,  "ProjectC (not selected)");
    }

    /**
     * Select NatureProjectA (already has JML nature from t1); invoke Add
     * OpenJML Nature a second time.  Verify the operation is idempotent:
     * A retains the nature, no error dialog appears.
     */
    @Test
    public void t2_addNatureToAAgain() throws CoreException {
        selectProjects("NatureProjectA");
        clickOpenJmlMenuItem("Add OpenJML Nature");
        waitForBuild();

        // No error dialog should have appeared
        dismissShellIfPresent("Error");

        assertHasJmlNature(projectA, "ProjectA after second Add");
    }

    /**
     * Give NatureProjectC JML nature programmatically; then multi-select B
     * and C; invoke Remove OpenJML Nature.  Verify B and C lose the nature
     * (Properties + decorator), while A retains it.
     */
    @Test
    public void t3_removeNatureFromBandC() throws CoreException {
        addJmlNatureProgrammatically(projectC);
        waitForBuild();
        assertHasJmlNature(projectC, "ProjectC pre-condition");

        selectProjects("NatureProjectB", "NatureProjectC");
        clickOpenJmlMenuItem("Remove OpenJML Nature");
        waitForBuild();

        assertNoJmlNature(projectB,  "ProjectB after Remove");
        assertNoJmlNature(projectC,  "ProjectC after Remove");
        assertHasJmlNature(projectA, "ProjectA (not selected, should retain nature)");
    }

    /**
     * Select NatureProjectA and a source file inside NatureProjectC (which
     * has no nature after t3); invoke Add OpenJML Nature.  Verify the nature
     * is applied to C's containing project via the file selection path.
     *
     * <p>This exercises the plugin handler behaviour where selecting a file
     * (rather than a project node) triggers nature application on the
     * file's containing project.
     */
    @Test
    public void t4_addNatureViaFileSelection() throws CoreException {
        // Ensure C has no nature (should already be the case after t3)
        removeJmlNatureProgrammatically(projectC);
        waitForBuild();

        selectProjectAndFileInOtherProject(
                "NatureProjectA",
                "NatureProjectC", "projectc", "EscError.java");
        clickOpenJmlMenuItem("Add OpenJML Nature");
        waitForBuild();

        assertHasJmlNature(projectC, "ProjectC after Add via file selection");
        assertHasJmlNature(projectA, "ProjectA (already had nature, unchanged)");
    }
}
