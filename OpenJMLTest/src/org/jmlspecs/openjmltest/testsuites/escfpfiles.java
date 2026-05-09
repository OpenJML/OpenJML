package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.*;
import java.util.*;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBase;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check running ESC on files in the file system for tests needing reasoning about floating point values.
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
public class escfpfiles extends EscBaseFiles {

    @Test @Ignore
    public void gitbug732() {
        helpEscSimple();
    }

    @Test @Ignore
    public void gitbug735() {
        expectedExit = 0;
        helpEscSimple();
    }
    
    @Test @Ignore
    public void escDouble() {
        helpEscSimple();
    }

    @Test @Ignore
    public void escDouble1() {
        helpEscSimple();
    }

    @Test @Ignore // timesout
    public void escDouble2() {
        helpEscSimple("--exclude=clone,remainderBy,toString");
    }

    @Test @Ignore
    public void escDouble2a() {
        helpEscName("escDouble2","--esc-max-warnings=1","--show","--method=remainderBy","--subexpressions");
    }
    
    @Test @Ignore
    public void escDouble3() {
        helpEscSimple("--method=remainderBy","--no-show-skipped","--esc-max-warnings=1");
    }
    
    @Test @Ignore
    public void escFloat() {
        helpEscSimple();
    }

    @Test @Ignore
    public void escfpMath() {
        helpEscSimple();
    }

    @Test @Ignore
    public void escfpPrimitiveOps() {
        helpEscSimple();
    }


    
    @Ignore // FIXME -  Needs more double specs
    @Test public void gitbug580() {
        expectedExit = 0;
        helpEscSimple();
    }
    
    @Ignore // FIXME - times out -- double arithmetic?
    @Test
    public void gitbug601() {
        expectedExit = 0;
        helpEscSimple();
    }
    
    @Ignore // FIXME -  double arithmetic?
    @Test
    public void gitbug633() {
        expectedExit = 0;
        helpEscSimple();
    }
    
    @Ignore // FIXME 
    @Test
    public void gitbug751() {
        expectedExit = 0;
        helpEscSimple();
    }
    

    @Test public void sfbug414() { // FIXME - is the code-math option needed? Why?
        expectedExit = 0;
        helpEscFile("test/sfbug414","test/sfbug414", "-cp", "test/sfbug414", "--esc","--progress","--logic=ALL","--esc-max-warnings=5", "--code-math=bigint");
    }

    @Test public void sfbug414n() { // FIXME - is the code-math option needed? Why?
        expectedExit = 0;
        helpEscFile("test/sfbug414","test/sfbug414", "-cp", "test/sfbug414", "--esc","--progress","--logic=AUFNIRA","--esc-max-warnings=5", "--code-math=bigint");
    }
}
