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
    
    public void helpEscSimple(String... opts) {
        addOptions("--code-math=safe");
        super.helpEscSimple(opts);
    }

    @Test
    public void gitbug814() {
        helpEscSimple("--allow-pure-in-specs","--exclude=size,ks,btw,depthOfNull");
    }

    @Test
    public void gitbug814a() {
        helpEscSimple("--allow-pure-in-specs","--method=BinaryTree.Node.size");
    }

    @Test
    public void gitbug814b() {
        helpEscSimple("--allow-pure-in-specs","--method=ks","--esc-max-warnings=1");
    }

    @Test
    public void gitbug814c() {
        helpEscSimple("--allow-pure-in-specs","--method=BinaryTree.Interval.size");
    }

    @Test
    public void gitbug814d() {
        helpEscSimple("--allow-pure-in-specs","--method=btw","--esc-max-warnings=1");
    }

    @Test
    public void gitbug814e() {
        helpEscSimple("--allow-pure-in-specs","--method=depthOfNull");
    }

    // This actually does not appear to be related to the other gitbug814 tests
    @Test
    public void gitbug814z() {
        helpEscSimple();
    }
    
    @Test @Ignore // non-linear integer arithmetic times out
    public void gitbug943() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug943a() {
        helpEscName("gitbug943", "--check-feasibility=none", "--method=myGCD");
    }
    
    @Test
    public void byteQuant() {
        helpEscSimple();
    }
    
    // The following are split into multiple tests to minimize the combinatorial non-determinism in the output
    @Test
    public void sfbug420() {
        helpEscSimple("--exclude=count;itemAt;main;isEmpty;push;top");
    }
    
    @Test
    public void sfbug420a() {
        helpEscSimple("--method=count");
    }
    
    @Test
    public void sfbug420b() {
        helpEscSimple("--method=itemAt");
    }
    
    @Test
    public void sfbug420c() {
        helpEscSimple("--method=main");
    }
    
    @Test
    public void sfbug420d() {
        helpEscSimple("--method=isEmpty");
    }
    
    @Test
    public void sfbug420e() {
        helpEscSimple("--method=push");
    }
    
    @Test
    public void sfbug420eOK() {
        helpEscSimple("--method=push"); // FIXME - not sure wheterh or not all methods should be checked here
    }
    
    @Test
    public void sfbug420f() {
        helpEscSimple("--method=top");
    }
    
    @Test
    public void sfbug420X() {
        helpEscSimple();
    }
    
    @Test  // TODO - could use some additional investigation as to what this submitted file set is supposed to do
    public void escrmloop() {
        helpEscSimple("--check-feasibility=none","--timeout=60");
    }
    
    @Test
    public void escrmloop2() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test @Ignore // not working yet
    public void escFPcompose() {
        helpEscSimple();
    }
    
    @Test
    public void escLemma() {
        helpEscSimple("--check-feasibility=none");
    }
    
    @Test
    public void escOld() {
        helpEscSimple();
    }
    
    @Test
    public void escOldState() {
        helpEscSimple();
    }
    
    @Test
    public void exceptionCancel() {
        helpEscSimple();
    }
    
    @Test
    public void buggyCalculator() {
        helpEscSimple();
    }

    @Test
    public void buggyCalculatorBV() {
        helpEscSimple("--esc-max-warnings=1","--timeout=600");
    }

    @Test
    public void buggyCalculatorBV2() {
        helpEscSimple("--esc-max-warnings=1","--timeout=600");
    }

    @Test
    public void buggyRandomNumbers() {
        helpEscSimple();
    }

    @Test @Ignore // times out -- see testPrime for fixed version
    public void buggyPrimeNumbers() {
        helpEscSimple();
    }

    @Test @Ignore // FIXME - unclear why fails
    public void buggyPalindrome() {
        helpEscSimple();
    }

    @Test
    public void escException() {
        helpEscSimple();
    }

    @Test
    public void preold() {
        helpEscSimple();
    }
    

    @Test
    public void preold2() {
        expectedExit = 1;
        helpEscSimple();
    }

    @Test
    public void nullableOld() {
        helpEscSimple();
    }

    @Test
    public void staticOld() {
        expectedExit = 1;
        helpEscSimple();
    }

    @Test
    public void gitbug942() {
        helpEscSimple();
    }

    @Test
    public void prelabel() {
        helpEscSimple();
    }

    @Test
    public void helper() {
        helpEscSimple();
    }


}
