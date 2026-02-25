package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;

import static org.junit.Assert.fail;
import org.junit.*;

/** These tests check running RAC on files in the file system, comparing the
 * output against expected files. These tests are a bit easier to create, since 
 * the file and output do not have to be converted into Strings; however, they
 * are not as easily read, since the content is tucked away in files, rather 
 * than immediately there in the test class.
 * <P>
 * To add a new test:
 * <UL>
 * <LI> create a directory containing the test files as a subdirectory of 
 * 'test'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racfilesmodels extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        super.setUp();
    }

    @Test @Ignore // model files
    public void gitbug524() {
        helpCompileRun("Test"); 
    }

    @Test @Ignore // model files
    public void gitbug584() {
        helpCompileRun("AClass");
    }

    @Test @Ignore // model files
    public void gitbug590() {
        runrac = false; // Expected compile error
        expectedExit = 1;
        helpCompileRun("Sequence");
    }

    @Test @Ignore // model files
    public void gitbug590a() {
        helpCompileRun("Sequence");
    }

}
