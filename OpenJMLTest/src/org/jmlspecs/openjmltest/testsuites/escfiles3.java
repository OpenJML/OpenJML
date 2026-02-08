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
public class escfiles3 extends EscBaseFiles {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    public void helpTG(String... opts) {
        addOptions("--code-math=safe");
        super.helpTG(opts);
    }

    @Test
    public void gitbug814() {
        helpTG("--exclude=size,ks,btw,depthOfNull");
    }

    @Test
    public void gitbug814a() {
        helpTG("--method=BinaryTree.Node.size");
    }

    @Test
    public void gitbug814b() {
        helpTG("--method=ks","--esc-max-warnings=1");
    }

    @Test
    public void gitbug814c() {
        helpTG("--method=BinaryTree.Interval.size");
    }

    @Test
    public void gitbug814d() {
        helpTG("--method=btw","--esc-max-warnings=1");
    }

    @Test
    public void gitbug814e() {
        helpTG("--method=depthOfNull");
    }

    // This actually does not appear to be related to the other gitbug814 tests
    @Test
    public void gitbug814z() {
        helpTG();
    }
    
    @Test
    public void byteQuant() {
        helpTG();
    }
    
    // The following are split into multiple tests to minimize the combinatorial non-determinism in the output
    @Test
    public void sfbug420() {
        helpTG("--exclude=count;itemAt;main;isEmpty;push;top");
    }
    
    @Test
    public void sfbug420a() {
        helpTG("--method=count");
    }
    
    @Test
    public void sfbug420b() {
        helpTG("--method=itemAt");
    }
    
    @Test
    public void sfbug420c() {
        helpTG("--method=main");
    }
    
    @Test
    public void sfbug420d() {
        helpTG("--method=isEmpty");
    }
    
    @Test
    public void sfbug420e() {
        helpTG("--method=push");
    }
    
    @Test
    public void sfbug420eOK() {
        helpTG("--method=push"); // FIXME - not sure wheterh or not all methods should be checked here
    }
    
    @Test
    public void sfbug420f() {
        helpTG("--method=top");
    }
    
    @Test
    public void sfbug420X() {
        helpTG();
    }
    
    @Test  // TODO - could use some additional investigation as to what this submitted file set is supposed to do
    public void escrmloop() {
        helpTG("--check-feasibility=none","--timeout=60");
    }
    
    @Test
    public void escrmloop2() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test @Ignore // not working yet
    public void escFPcompose() {
        helpTG();
    }
    
    @Test
    public void escLemma() {
        helpTG("--check-feasibility=none");
    }
    
    @Test
    public void escOld() {
        helpTG();
    }
    
    @Test
    public void escOldState() {
        helpTG();
    }
    
    @Test
    public void exceptionCancel() {
        helpTG();
    }
    
    @Test @Ignore // Problem is with mixed BV and bigint operations
    public void buggyCalculator() {
        helpTG();
    }

    @Test
    public void buggyRandomNumbers() {
        helpTG();
    }

    @Test @Ignore // times out -- see testPrime for fixed version
    public void buggyPrimeNumbers() {
        helpTG();
    }

    @Test @Ignore // FIXME - unclear why fails
    public void buggyPalindrome() {
        helpTG();
    }

    @Test
    public void escException() {
        helpTG();
    }

    @Test
    public void preold() {
        helpTG();
    }
    

    @Test
    public void preold2() {
        expectedExit = 1;
        helpTG();
    }

    @Test
    public void nullableOld() {
        helpTG();
    }

    @Test
    public void staticOld() {
        expectedExit = 1;
        helpTG();
    }


}
