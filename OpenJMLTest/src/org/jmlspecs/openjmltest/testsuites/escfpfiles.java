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

    @Test
    public void gitbug732() {
        helpTCG();
    }

    @Test
    public void gitbug735() {
        expectedExit = 0;
        helpTCG("--show","--method=impl"); // For debugging
    }
    
    @Test
    public void escDouble() {
        helpTCG();
    }

    @Test
    public void escDouble1() {
        helpTCG();
    }

    @Test @Ignore // timesout
    public void escDouble2() {
        helpTF("escDouble2","--exclude=clone,remainderBy,toString");
    }

    @Test @Ignore
    public void escDouble2a() {
        helpTF("escDouble2","--esc-max-warnings=1","--show","--method=remainderBy","--subexpressions");
    }
    
    @Test
    public void escDouble3() {
        helpTF("escDouble3","--method=remainderBy","--no-show-skipped","--esc-max-warnings=1");
    }
    
    @Test
    public void escFloat() {
        helpTCG();
    }

    @Test
    public void escfpMath() {
        helpTCG();
    }

    @Test
    public void escfpPrimitiveOps() {
        helpTCG();
    }


    
    @Ignore // FIXME -  Needs more double specs
    @Test public void gitbug580() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Ignore // FIXME - times out -- double arithmetic?
    @Test
    public void gitbug601() {
        expectedExit = 0;
        helpTCG();
    }
    


}
