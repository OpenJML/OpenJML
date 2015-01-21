package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Before;
import org.junit.Test;

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

public class racfiles extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        setUpForFiles();
        super.setUp();
    }




    /** Testing without using system specs */
    @Test
    public void test1() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpTCF("test/rac1","test/rac1","Bug1","-noInternalSpecs");
    }

    /** Testing using system specs */
    @Test  // FIXME - problems with library specs - RAC cannot handle ghost variables when it does not compile the class file
    public void test1a() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpTCF("test/rac1a","test/rac1a","Bug1");
    }

    @Test // Originally a Stack overflow because of recursive check of invariant
    public void testBug1() {
        expectedExit = 0;
        expectedRACExit = 1;
        helpTCF("test/racbug1","test/racbug1","Add");
    }

    @Test // Originally a Stack overflow because of recursive check of invariant
    public void testBugStackTrace() {
        expectedExit = 0;
        helpTCF("test/racStackTrace","test/racStackTrace","CantCompileRAC");
    }

    @Test // Originally crashed because of a model method in a library class
    public void testPoint() {
        expectedExit = 0;
        helpTCF("test/racPoint","test/racPoint","Point","-quiet");
    }

    @Test // Originally crashed because of a model method in a library class
    public void testPoint2() {
        expectedExit = 0;
        helpTCF("test/racPoint2","test/racPoint2","Point");
    }

    @Test
    public void testFirstTest() {
        expectedExit = 0;
        helpTCF("test/firstTest","test/firstTest","FirstTest","-racJavaChecks","-racCheckAssumptions");
    }

    @Test
    public void testUniqueList() {
        expectedExit = 0;
        helpTCF("test/uniqueList","test/uniqueList","UniqueList","-racJavaChecks","-racCheckAssumptions");
    }

    @Test 
    public void testUniqueList1() {
        expectedExit = 0;
        helpTCF("test/uniqueListBug1","test/uniqueListBug1","UniqueListBug1","-racJavaChecks","-racCheckAssumptions");
    }

    @Test 
    public void testUniqueList2() {
        expectedExit = 0;
        helpTCF("test/uniqueListBug2","test/uniqueListBug2","UniqueListBug2");
    }

    @Test
    public void testDecimal() {
        expectedExit = 0;
        helpTCF("test/sv_rac","test/sv_rac","sv_rac/Decimal");
    }

    @Test
    public void testDecimal2() {
        expectedExit = 0;
        helpTCF("test/sv_rac_mod","test/sv_rac_mod","sv_rac/Decimal");
    }

    @Test
    public void testbigint() {
        expectedExit = 0;
        helpTCF("test/racbigint","test/racbigint","bigint");
    }

    @Test
    public void testreal() {
        expectedExit = 0;
        helpTCF("test/racreal","test/racreal","real");
    }

    @Test
    public void demoStudent() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/student","test/demoStudent","ExecuteCStudent2","-racJavaChecks","-racCheckAssumptions");
    }

    @Test
    public void testECU() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/ecudemo","test/ecurac","Test","-racJavaChecks","-racCheckAssumptions");
    }

    @Test
    public void purseCardTest() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/purse","test/purse","CardTest");
    }

    @Test
    public void purseModTest() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/purseMod","test/purseMod","CardTest");
    }

    @Test
    public void racTime() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/Time.java","test/racTime","Time");
    }

    @Test
    public void racQueue() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/Queue.java","test/racQueue","Queue");
    }

    @Test
    public void racAddng() {
        rac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata"+z+"test/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("test/racaddng/Add_InstanceStrategy.java","test/racaddng","Add_JML_Test","-cp","../OpenJML/bin-runtime;test/racaddng;test/racaddng/jmlunitng.jar");
    }

    @Test
    public void racAddngall() {
        rac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata"+z+"test/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("test/racaddng","test/racaddngall","Add_JML_Test","-cp","../OpenJML/bin-runtime;test/racaddngall;test/racaddng;test/racaddng/jmlunitng.jar");
    }

    @Test
    public void racNoModel() {
        rac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata"+z+"test/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("test/racNoModel","test/racNoModel","NoModelTest");
    }

    @Test
    public void racMainActivity() {
        runrac = false; // FIXME: Don't try running executable until we supply some input
        //rac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime"+z+"testdata"+z+"test/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("test/racMainActivity","test/racMainActivity","MainActivity");
    }


    @Test
    public void racMainActivityMicro() {
        expectedExit = 0;
        helpTCF("test/racMainActivityMicro","test/racMainActivityMicro","CharAt");
    }

    @Test // FIXME - should we allow and compensate for \result in an \old environment
    public void racOld() {
        expectedExit = 1;
        runrac = false;
        helpTCF("test/racold","test/racold","ArrayExample");
    }

}
