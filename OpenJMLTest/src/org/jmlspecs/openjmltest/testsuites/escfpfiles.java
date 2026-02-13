package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

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
import org.jmlspecs.openjmltest.EscBase;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assume;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
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
        helpTG();
    }

    @Test @Ignore
    public void gitbug735() {
        expectedExit = 0;
        helpTG();
    }
    
    @Test @Ignore
    public void escDouble() {
        helpTG();
    }

    @Test @Ignore
    public void escDouble1() {
        helpTG();
    }

    @Test @Ignore // timesout
    public void escDouble2() {
        helpTG("--exclude=clone,remainderBy,toString");
    }

    @Test @Ignore
    public void escDouble2a() {
        helpTF("escDouble2","--esc-max-warnings=1","--show","--method=remainderBy","--subexpressions");
    }
    
    @Test @Ignore
    public void escDouble3() {
        helpTG("--method=remainderBy","--no-show-skipped","--esc-max-warnings=1");
    }
    
    @Test @Ignore
    public void escFloat() {
        helpTG();
    }

    @Test @Ignore
    public void escfpMath() {
        helpTG();
    }

    @Test @Ignore
    public void escfpPrimitiveOps() {
        helpTG();
    }


    
    @Ignore // FIXME -  Needs more double specs
    @Test public void gitbug580() {
        expectedExit = 0;
        helpTG();
    }
    
    @Ignore // FIXME - times out -- double arithmetic?
    @Test
    public void gitbug601() {
        expectedExit = 0;
        helpTG();
    }
    
    @Ignore // FIXME -  double arithmetic?
    @Test
    public void gitbug633() {
        expectedExit = 0;
        helpTG();
    }
    
    @Ignore // FIXME 
    @Test
    public void gitbug751() {
        expectedExit = 0;
        helpTG();
    }
    

    @Test public void sfbug414() {
        expectedExit = 0;
        helpTCF("test/sfbug414","test/sfbug414", "-cp", "test/sfbug414", "--esc","--progress","--logic=ALL","--esc-max-warnings=5");
    }

    @Test public void sfbug414n() {
        expectedExit = 0;
        helpTCF("test/sfbug414","test/sfbug414", "-cp", "test/sfbug414", "--esc","--progress","--logic=AUFNIRA","--esc-max-warnings=5");
    }
}
