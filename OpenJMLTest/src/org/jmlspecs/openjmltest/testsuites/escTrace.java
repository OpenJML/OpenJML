package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escTrace extends EscBase {

    @Override
    public void setUp() throws Exception {
        captureOutput = true;
        checkOutput = false;
        super.setUp();
        addOptions("--subexpressions");
    }

    public static final String dir = "test/escTraceTests";

    /** This String declaration and assignment */
    @Test
    public void testSimpleTrace() {
        main.addOptions("--method=m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math */ public class TestJava {
                  public void m1(int i) {
                       int j = 5;
                       j = j + i;
                       //@ assert j != 7;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m1",12
                );
        String output = output();
        String error = errorOutput();
        Assert.assertEquals("Mismatched error output","",error);

        outputCompare.compareTextToMultipleFiles(output, dir, "testSimpleTrace-expected", dir + "/testSimpleTrace-actual");
   }

    // FIXME - the ??? is the trace values

    /** This String declaration and assignment */
    @Test
    public void testFieldTrace() {
        main.addOptions("-method=m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math */ public class TestJava {
                       int k;
                  public void m1(int i) {
                       k = 5 + i;
                       //@ assert k != 7;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m1",12
                );
        String output = output();
        String error = errorOutput();
        Assert.assertEquals("Mismatched error output","",error);
        outputCompare.compareTextToMultipleFiles(output, dir, "testFieldTrace-expected", dir + "/testFieldTrace-actual");
    }

    /** This String declaration and assignment */
    @Test
    public void testEnsuresTrace() {
        main.addOptions("-method=m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math */ public class TestJava {
                       int k;
                  //@ requires i == 1;
                  //@ ensures \\result < i-i;
                  public int m1(int i) {
                       k = 5 + i;
                       return k * 2;
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method m1",8
                ,"/tt/TestJava.java:5: verify: Associated declaration",7
                );
        String output = output();
        String error = errorOutput();
        Assert.assertEquals("Mismatched error output","",error);
        outputCompare.compareTextToMultipleFiles(output, dir, "testEnsuresTrace-expected", dir + "/testEnsuresTrace-actual");
    }

    /** This String declaration and assignment */
    @Test
    public void testEnsuresSafeTrace() {
        main.addOptions("-method=m1"); // Part of test
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_safe_math */ public class TestJava {
                       int k;
                  //@ requires i == Integer.MAX_VALUE;
                  //@ ensures \\result < 0;
                  public int m1(int i) {
                       k = 5 + i;
                       return k;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method m1: overflow in int sum",14
                );
        String output = output();
        String error = errorOutput();
        outputCompare.compareTextToMultipleFiles(output, dir, "testEnsuresSafeTrace-expected", dir + "/testEnsuresSafeTrace-actual");
        Assert.assertEquals("Mismatched error output","",error);
    }
}
