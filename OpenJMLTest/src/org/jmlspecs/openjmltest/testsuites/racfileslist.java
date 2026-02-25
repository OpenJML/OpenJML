package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;
import org.jmlspecs.openjmltest.Utils;
import java.io.*;
import java.util.*;

import static org.junit.Assert.fail;
import org.junit.*;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check running RAC on files in the file system, comparing the
 * output against expected files. This suite checks for any folders under OpenJMLTest/test
 * that contain a 'rac' file or have 'rac' in their name,
 * and are not already tested in the suites listed in
 * 'testsuitesToExclude'
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@org.junit.runner.RunWith(Parameterized.class)
public class racfileslist extends RacBase implements Utils {

    @Override
    @Before
    public void setUp() throws Exception {
        super.setUp();
    }
    
    /** These are the suites whose files are already being run, and so are excluded from this suite */
    public static String[] testsuitesToExclude = new String[]{
            "org.jmlspecs.openjmltest.testsuites.primrac",
            "org.jmlspecs.openjmltest.testsuites.racfiles",
            "org.jmlspecs.openjmltest.testsuites.racfilesmodels"
    };

    /** A routine that computes a List of one-element String arrays, where each of those elements is a 
     * test directory that is not already used in a test by any of the testsuites in the 'testsuitesToExclude' array above.
     * The output of this method serves as the parameter list for the parameterized unit test.
     */
    @Parameters
    static public Collection<String[]> data() {
        try {
            java.util.List<String[]> tests = Utils.findTests((File f, String nm) -> f.isDirectory() &&
                    (new java.io.File(f, "rac").exists() || nm.startsWith("rac")) && !new java.io.File(f, "skip").exists(),
                    testsuitesToExclude);
            // Just for information, print out all the tests that have been identified
            List<String> remaining = tests.stream().map(t -> t[0]).collect(java.util.stream.Collectors.toList());
            // System.out.println("ORPHANED RAC FILES FOLDERS: " + remaining); // Expect the racfilesorphan harness test
            // Comment out this assert if you want the orphaned tests to actually run, but it is better to make
            // explicit tests in racfiles
            Assert.assertTrue(remaining.size() != 1 || !"racfilesorphan".equals(remaining.get(0)));
            return tests;
        } catch (Exception e) {
            // Using a throw instead of Assert.fail to avoid complaint about missing return
            throw new AssertionError("Exception while determining test methods in racfileslist: " + e);
        }
    }
    
    String testName;
    
    public racfileslist(String testName) {
        this.testName = testName;
    }
    
    /** The actual test method -- don't rely on this method for anything other than harness tests
     * because it just attempts to compile the test file.
     */
    @Test
    public void test() {
        helpRac("test/" + testName,"test/" + testName, null);
    }

}
