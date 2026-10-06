package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.*;

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
    public void gitbug950() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug955() {
        helpEscSimple("--allow-pure-in-specs");
    }
    
    @Test
    public void gitbug955a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug671a() {
        // A conditional with a generic method call as a branch, as a method argument (#671)
        helpEscSimple();
    }

    @Test
    public void gitbug963() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug963a() {
        helpEscSimple();
    }

    @Test
    public void gitbug963b() {
        // A conditional with a \seq concatenation as a branch (part of #963)
        helpEscSimple();
    }
    
    @Test
    public void gitissue62() {
        helpEscSimple();
    }
    
    @Test
    public void gitissue62b() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug969() {
        helpEscSimple();
    }

    @Test
    public void gitbug969a() {
        helpEscSimple();
    }

    @Test
    public void gitbug969b() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug971() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug971a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug971b() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug971c() {
        helpEscSimple();
    }

    @Test
    public void gitbug979() {
        helpEscSimple();
    }

    @Test
    public void gitbug979a() {
        helpEscSimple();
    }

    @Test
    public void gitbug979b() {
        helpEscSimple();
    }

    @Test
    public void gitbug980b() {
        helpEscSimple();
    }

    @Test
    public void gitbug980c() {
        helpEscSimple();
    }

    @Test
    public void gitbug996() {
        helpEscSimple();
    }

    @Test
    public void gitbug997() {
        // Only the proofs are of interest here: the feasibility checks of methods whose specifications use
        // Math.gcd cannot be settled (a model of gcd's quantified specification) and run to the timeout
        helpEscSimple("--check-feasibility=none");
    }

    @Test
    public void gitbug997a() {
        // User-written gcd specifications with % and / by a quantified variable: refuted promptly, not
        // a matching loop; quantified % and / are still instantiated from % and / outside the quantifier
        helpEscSimple("--check-feasibility=none");
    }

    @Test
    public void gitbug997b() {
        // Warnings: quantifiers with no term that can serve as a trigger; a feasibility check not decided
        // because of nonlinear arithmetic (the short timeout ends it quickly)
        helpEscSimple("--timeout=5","--check-feasibility=precondition");
    }

    @Test
    public void gitbug1000() {
        helpEscSimple();
    }

    @Test
    public void gitbug1001() {
        // \sum, \product and \num_of, translated into recursive SMT functions (a port of PR #773)
        helpEscSimple();
    }

    @Test
    public void gitbug1001b() {
        // Loop invariants with \sum and \product that ESC does not yet prove (a short timeout keeps the
        // result 'Validity is unknown' on any machine)
        helpEscSimple("--timeout=10","--check-feasibility=none");
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
        helpEscSimple("--warn=implicit-helper");
    }

    @Test
    public void argnullity() {
        helpEscSimple();
    }
    
    @Test
    public void returnNullity() {
        helpEscSimple();
    }
}
