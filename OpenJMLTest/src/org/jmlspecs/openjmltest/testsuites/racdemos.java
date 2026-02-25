package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;
import java.io.File;

import static org.junit.Assert.fail;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.Ignorable;

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

// @RunWith(Ignorable.class)
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racdemos extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        super.setUp();
        Assume.assumeTrue( new File(OpenJMLDemoPath).exists() );
    }
    
    public void helpCompileRunDemo(String dir, String mainClassname, String ... opts) {
        String adir = OpenJMLDemoPath + dir;
        if (opts.length == 0) helpRac(adir, adir, mainClassname, "-cp", adir);
        else helpRac(adir, adir, mainClassname, org.jmlspecs.openjml.Utils.concat(new String[] { "-cp", adir}, opts));
    }

    
    @Test
    public void demoPurseMod() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpCompileRunDemo("/src/openjml/purseMod","CardTest");
    }
    
    @Test
    public void demoPurse() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpCompileRunDemo("/src/openjml/purse","CardTest");
    }

    @Test
    public void demoecu() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpCompileRunDemo("/src/openjml/ecu","Test");
    }

    @Test
    public void demoecu2() {
        expectedExit = 1;
        helpCompileRunDemo("/src/openjml/ecu2",null);
    }

    @Test
    public void demoecu2a() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpCompileRunDemo("/src/openjml/ecu2a","IgnitionTest");
    }

    @Test
    public void demoQueue() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpRac(OpenJMLDemoPath + "/src/openjml/demo/Queue.java", "test/racQueue","Queue");
    }

    @Test
    public void demoTime() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpRac(OpenJMLDemoPath + "/src/openjml/demo/Time.java", "test/racTime","Time");
    }


    @Test @Ignore // not working yet
    public void racSokoban() {
        expectedExit = 0;
        expectedRACExit = 1;
        helpCompileRunDemo("/src/sokoban/src","Game","-progress");
    }

    @Test @Ignore // not working yet
    public void racSokoban2() {
        expectedExit = 0;
        expectedRACExit = 1;
        ignoreNotes = true;
        helpCompileRunDemo("/src/sokoban2/src","Game","-progress");
    }

    @Test @Ignore // not working yet
    public void racSokoban3() {
        expectedExit = 0;
        expectedRACExit = 1;
        ignoreNotes = true;
        helpCompileRunDemo("/src/sokoban3/src","Game","-progress");
    }

    @Test @Ignore // not working yet
    public void racSokoban3Bug() {  // FIXME - currently the expected result says too big for a try statement, but originally it had a crash
        String dir = OpenJMLDemoPath + "/src/sokoban3/src";
        expectedExit = 1;
        runrac = false;
        expectedRACExit = 0;
        helpRac(dir,dir+"/../bug","Game","-cp",dir,"-progress","-racJavaChecks");
    }


}
