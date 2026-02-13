package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assume;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check running ESC on files in the file system, comparing the
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
@RunWith(ParameterizedWithNames.class)
public class escfiles2 extends EscBaseFiles {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    public void helpTG(String... opts) {
        super.helpTG(opts);
    }

    
    @Test
    public void gitbug362() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void gitbug450a() {
        helpTG();
    }
    
    @Test
    public void gitbug450b() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void gitbug455a() {
        helpTG();
    }

    @Test
    public void gitbug582() {
        expectedExit = 0;
    }


    @Test
    public void gitbug600() {
        helpTG();
    }
    
    @Test
    public void gitbug724() {
        helpTG("--warn=missing-measured-by");
    }
    
    @Test
    public void gitbug725() {
        helpTG();
    }
    
    @Test
    public void gitbug726() {
        helpTG("--check-feasibility=none");
    }
    
    @Test
    public void gitbug726a() {
        helpTG();
    }
    
    @Test
    public void gitbug761() {
        helpTG("--check");
    }
    
    @Test
    public void gitbug762() {
        helpTG("--check");
    }
    
    @Test
    public void gitbug763() {
        helpTG("--check-feasibility=none");
    }
    
    @Test
    public void gitbug766() {
        helpTG();
    }
    
    @Test
    public void gitbug777() {
        helpTG();
    }
    
    @Test
    public void gitbug780a() {
        helpTG("--method=marray");
    }
    
    @Test @Ignore // FIXME - times out in attempting to prove
    public void gitbug802() {
        helpTG();
    }
    
    @Test
    public void gitbug812() {
        helpTG("--code-math=safe");
    }
    
    @Test 
    public void gitbug812a() {
        helpTG("--code-math=safe","--check-feasibility=none");
    }
    
    @Test
    public void gitbug816() {
        helpTG();
    }
    
    @Test
    public void gitbug861() {
        helpTG();
    }
    
    @Test
    public void gitbug869() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void gitbug812crash() {
        expectedExit = 1;
        helpTG();
    }

    @Test
    public void gitbug872() {
        helpTG();
    }

    @Test
    public void gitbug873() {
        helpTG("--check");
    }
    
    @Test
    public void gitbug875() {
        helpTG();
    }
    
    @Test
    public void gitbug876() {
        helpTG("--normal","--method=isNonPrime","--check-feasibility=none");
    }
    
    // gitbug877 is in escall3 as testSwitch
    
    @Test
    public void gitbug879() {
        helpTG();
    }
    
    @Test
    public void gitbug880() {
        helpTG();//"--code-math=safe");
    }
    
    @Test
    public void gitbug883() {
        helpTG("--esc-max-warnings=1","--check-feasibility=precondition,exit","--nullable-by-default","--timeout=60");
    }
    
    @Test
    public void gitbug889() {
        helpTG();
    }
    
    @Test
    public void gitbug890() {
        helpTG();
    }
    
    @Test
    public void gitbug894() {
        helpTG("--method=Test3.*");
    }
    
    @Test
    public void gitbug895() {
        helpTG();
    }
    
    @Test
    public void gitbug898() {
        expectedExit = 1;
        helpTG("--spec-math=java","--code-math=java");
    }
    
    @Test
    public void gitbug898a() {
        expectedExit = 1;
        helpTG("--spec-math=java","--code-math=java");
    }
    
    @Test
    public void gitbug898b() {
        helpTG("--spec-math=java","--code-math=java");
    }
    
    @Test
    public void gitbug899() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void gitbug901() {
        helpTG();
    }
    
    @Test
    public void gitbug901a() {
        helpTG();
    }
    
    @Test
    public void gitbug902() {
        helpTG("--check");
    }
    
    @Test
    public void gitbug903() {
        helpTG();
    }
    
    @Test
    public void gitbug922() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void gitbug932() {
        helpTG();
    }
    
    @Test
    public void gitbug934() {
        helpTG();
    }
    
    @Test
    public void gitbug935() {
        helpTG();
    }
    
    @Test
    public void gitbug938() {
        helpTG();
    }
    
    @Test
    public void gitbug941() {
        helpTG();
    }
    
    @Test
    public void importProblem() {
        helpTG();
    }
    
    @Test
    public void importProblem2() {
        helpTG();
    }
    
    @Test
    public void imports() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void recommends() {
        helpTG("--show=program","--code-math=bigint");
    }
    
    @Test
    public void recommendsA() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void recommendsB() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void recommendsC() {
        helpTG();
    }
    
    @Test
    public void escRawding2() {
        helpTG();
    }
    
    @Test
    public void escRawdingA() {
        helpTG();
    }
    
    @Test
    public void escRawdingB() {
        helpTG();
    }
    
    @Test
    public void escharness1() {
        try {
            helpTG("--check");
        } catch (AssertionError a) {
            assertEquals("Incorrect harness failure:", "There are no expected output files in test/escharness1", a.getMessage());
        }
    }
    
    @Test
    public void escharness2() {
        // When a comparison difference is found, the behavior is to print out the differences to 'out'
        // For the purpose of this test, we redirect that output.
        var savedout = this.out;
        this.out = tempout;
        try {
            helpTG("--check");
        } catch (AssertionError a) {
            String expected =
                    """
                    Files differ""";
            assertEquals("Incorrect harness failure:", expected, a.getMessage());
        } finally {
            this.out = savedout;
        }
    }

    // FIXME - don't think this is helpful because it does not call setupForFiles
    @Test
    public void escharness3() {
        solver = "z3_4_3";
        helpTG("--normal");
    }
    
    @Test public void typecheckWithJML() {
        expectedExit = 1;
        helpTG("--check");
    }
    
    @Test public void sfpatch25() {
        helpTG("--normal");
    }
    
    @Ignore // FIXME very long
    @Test public void sfbug402() {
        helpTG();
    }
    
    @Ignore // FIXME very long
    @Test public void sfbug402a() {
        helpTG();
    }
    
    @Ignore // FIXME very long
    @Test public void sfbug402b() {
        helpTG();
    }
    
    @Test public void sfbug407() {
        helpTG();
    }
    
    @Ignore // times out
    @Test public void sfbug396() {
        helpTG();
    }
    
    @Test public void sfbug398() {
        helpTG();
    }
    
    @Test public void sfbug399() {
        helpTG();
    }
    
    @Test public void sfbug404() {
        helpTG();
    }
    
    @Test public void sfbug408() {
        helpTG();
    }
    
    @Test public void sfbug409() {
        helpTG("--check-feasibility=precondition,exit,reachable,assert,assume");
    }
    
    @Test public void sfbug410() {
        helpTG();
    }
    
    @Test public void optiondir() {
        helpTG("--check", "--dirs", "test/optiondir/p", "q");
    }
    
    @Test public void changeMathMode() {
        helpTG("--check-feasibility=none");
    }
    
    @Test public void termination() {
        helpTG("--warn=missing-measured-by");
    }
    
    @Test public void terminationBad() {
        helpTG("--warn=missing-measured-by");
    }
    
    @Test public void legacyVerify() {
        helpTG("--verify-exit=-1");
    }
}
