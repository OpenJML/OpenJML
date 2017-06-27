package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;

// FIXME - these were old tests - are they duplicates? should we use them?

@RunWith(ParameterizedWithNames.class)
public class escArithmeticModes extends EscBase {

//    public escArithmeticModes() {
//        super("",isWindows?null:"cvc4");
//    }

    public escArithmeticModes(String options, String solver) {
        super(options,solver);
    }
    
    // FIXME - the -custom option fails significantly when escdebug and -trace are on
    // FIXME = significant failures in boogie and newesc
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-nullableByDefault"); // Because the tests were written this way
        //main.addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
 
    
    @Test @Ignore // Hangs with z3 4.5
    public void testNeg() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m",13
              );
    }

    @Test
    public void testNegNeg() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires i >= 0;\n"
                +"  public int m(int i) {\n"
                +"    int k = -(-i);\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testNegJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;\n"
                +"public class TestJava { \n"
                +"  /*@ code_java_math */ public int m(int i) {\n"
                +"    int k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testNegSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m",13
              );
    }

    @Test
    public void testNegMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;\n"
                +"@CodeBigintMath public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testSumSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = i + i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int ma(int i) {\n"
                +"    //@ assume i <= 0x3FFFFFFF;\n"
                +"    int k = i + i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int mb(int i) {\n"
                +"    //@ assume i >= (int)(0xC0000000);\n"
                +"    int k = i + i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int mc(int i) {\n"
                +"    //@ assume i <= 0x3FFFFFFF;\n"
                +"    //@ assume i >= (int)(0xC0000000);\n"
                +"    int k = i + i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int mm(int i, int j) {\n"
                +"    //@ assume (i < 0) != (j < 0);\n"
                +"    int k = i + j;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,anyorder(seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m:  underflow in int sum",15)
                         ,seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m:  overflow in int sum",15))
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma:  underflow in int sum",15
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method mb:  overflow in int sum",15
              );
    }

    @Test
    public void testSumJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = i + i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int mb(int i) {\n"
                +"    //@ assume i >= 0;\n"
                +"    int k = i + i;\n"
                +"    //@ assert k >= 0;\n" // FIXME - this should fail
                +"    return k; \n"
                +"  }\n"
                +"  public int mm(int i, int j) {\n"
                +"    int k = i + j;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testSumMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = i + i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int mb(int i) {\n"
                +"    //@ assume i >= 0;\n"
                +"    int k = i + i;\n"
                +"    //@ assert k >= 0;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int mm(int i, int j) {\n"
                +"    int k = i + j;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testDivSafe() {
        //main.addOptions("-logic=AUFNIA");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath public class TestJava { \n"
                +"  public int m(int i, int j) {\n"
                +"    int k = i/j;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,anyorder(
                  seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m:  overflow in int divide",14)
                 ,seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m",14)
                 )
              );
    }


}

