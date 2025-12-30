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
public class jmldoctests extends EscBaseFiles {

    // FIXME - will run jmldoc, not esc
    
    @Test @Ignore
    public void jmldoc1() {
        helpTG();
    }

    @Test @Ignore
    public void jmldoc2() {
        helpTG();
    }

    @Test @Ignore
    public void jmldoc3() {
        helpTG();
    }

    @Test @Ignore
    public void jmldoc4() {
        helpTG();
    }

    @Test @Ignore
    public void jmldoc5() {
        helpTG();
    }

    @Test @Ignore
    public void jmldoc6() {
        helpTG();
    }

    @Test @Ignore
    public void jmldoc7() {
        helpTG();
    }

}
