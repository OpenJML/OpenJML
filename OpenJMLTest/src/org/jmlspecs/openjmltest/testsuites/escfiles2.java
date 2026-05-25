package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.*;

import java.io.BufferedWriter;
import java.io.*;
import java.util.*;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.*;
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
    
    public void helpEscSimple(String... opts) {
        super.helpEscSimple(opts);
    }

    
    @Test
    public void gitbug362() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void gitbug450a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug450b() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void gitbug455a() {
        helpEscSimple();
    }

    @Test
    public void gitbug582() {
        expectedExit = 0;
    }


    @Test
    public void gitbug600() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug724() {
        helpEscSimple("--warn=missing-measured-by");
    }
    
    @Test
    public void gitbug725() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug726() {
        helpEscSimple("--check-feasibility=none");
    }
    
    @Test
    public void gitbug726a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug761() {
        helpEscSimple("--check");
    }
    
    @Test
    public void gitbug762() {
        helpEscSimple("--check");
    }
    
    @Test
    public void gitbug763() {
        helpEscSimple("--check-feasibility=none");
    }
    
    @Test
    public void gitbug766() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug777() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug780a() {
        helpEscSimple("--method=marray");
    }
    
    @Test @Ignore // FIXME - times out in attempting to prove
    public void gitbug802() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug812() {
        helpEscSimple("--code-math=safe");
    }
    
    @Test 
    public void gitbug812a() {
        helpEscSimple("--code-math=safe","--check-feasibility=none");
    }
    
    @Test
    public void gitbug816() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug861() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug869() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void gitbug812crash() {
        expectedExit = 1;
        helpEscSimple();
    }

    @Test
    public void gitbug872() {
        helpEscSimple();
    }

    @Test
    public void gitbug873() {
        helpEscSimple("--check");
    }
    
    @Test
    public void gitbug875() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug876() {
        helpEscSimple("--normal","--method=isNonPrime","--check-feasibility=none");
    }
    
    // gitbug877 is in escall3 as testSwitch
    
    @Test
    public void gitbug879() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug880() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug883() {
        helpEscSimple("--esc-max-warnings=1","--check-feasibility=precondition,exit","--nullable-by-default","--timeout=60");
    }
    
    @Test
    public void gitbug889() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug890() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug894() {
        helpEscSimple("--method=Test3.*");
    }
    
    @Test
    public void gitbug895() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug898() {
        expectedExit = 1;
        helpEscSimple("--spec-math=java","--code-math=java");
    }
    
    @Test
    public void gitbug898a() {
        expectedExit = 1;
        helpEscSimple("--spec-math=java","--code-math=java");
    }
    
    @Test
    public void gitbug898b() {
        helpEscSimple("--spec-math=java","--code-math=java");
    }
    
    @Test
    public void gitbug899() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void gitbug901() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug901a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug902() {
        helpEscSimple("--check");
    }
    
    @Test
    public void gitbug903() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug922() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void gitbug932() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug932a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug934() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug935() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug938() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug941() {
        helpEscSimple();
    }
    
    @Test
    public void importProblem() {
        helpEscSimple();
    }
    
    @Test
    public void importProblem2() {
        helpEscSimple();
    }
    
    @Test
    public void imports() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void recommends() {
        helpEscSimple("--show=program","--code-math=bigint");
    }
    
    @Test
    public void recommendsA() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void recommendsB() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void recommendsC() {
        helpEscSimple();
    }
    
    @Test
    public void escRawding2() {
        helpEscSimple();
    }
    
    @Test
    public void escRawdingA() {
        helpEscSimple();
    }
    
    @Test
    public void escRawdingB() {
        helpEscSimple();
    }
    
    @Test
    public void escharness1() {
        try {
            helpEscSimple("--check");
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
            helpEscSimple("--check");
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
        solver = null;
        helpEscSimple("--normal");
    }
    
    @Test public void typecheckWithJML() {
        expectedExit = 1;
        helpEscSimple("--check");
    }
    
    @Test public void sfpatch25() {
        helpEscSimple("--normal");
    }
    
    @Ignore // FIXME very long
    @Test public void sfbug402() {
        helpEscSimple();
    }
    
    @Ignore // FIXME very long
    @Test public void sfbug402a() {
        helpEscSimple();
    }
    
    @Ignore // FIXME very long
    @Test public void sfbug402b() {
        helpEscSimple();
    }
    
    @Test public void sfbug407() {
        helpEscSimple();
    }
    
    @Ignore // times out
    @Test public void sfbug396() {
        helpEscSimple();
    }
    
    @Test public void sfbug398() {
        helpEscSimple();
    }
    
    @Test public void sfbug399() {
        helpEscSimple();
    }
    
    @Test public void sfbug404() {
        helpEscSimple();
    }
    
    @Test public void sfbug408() {
        helpEscSimple();
    }
    
    @Test public void sfbug409() {
        helpEscSimple("--check-feasibility=precondition,exit,reachable,assert,assume");
    }
    
    @Test public void sfbug410() {
        helpEscSimple();
    }
    
    @Test public void optiondir() {
        helpEscSimple("--check", "--dirs", "test/optiondir/p", "q");
    }
    
    @Test public void changeMathMode() {
        helpEscSimple("--check-feasibility=none");
    }
    
    @Test public void termination() {
        helpEscSimple("--warn=missing-measured-by");
    }
    
    @Test public void terminationBad() {
        helpEscSimple("--warn=missing-measured-by");
    }
    
    @Test public void legacyVerify() {
        helpEscSimple("--verify-exit=-1");
    }
}
