package tests;

import java.util.Collection;

import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.sun.tools.javac.util.Options;

// FIXME - these were old tests - are they duplicates? should we use them?

// FIXME - restore parameterization when CVC is fixed
//@RunWith(Parameterized.class)
public class escArithmeticModes extends EscBase {

    public escArithmeticModes() {
        super("",isWindows?null:"cvc4");
    }

//    public esc(String option, String solver) {
//        super(option,solver);
//    }
    
    // FIXME - the -custom option fails significantly when escdebug and -trace are on
    // FIXME = significant failures in boogie and newesc
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-no-purityCheck");
        main.addOptions("-jmltesting");
        main.addOptions("-nullableByDefault"); // Because the tests were written this way
        //main.addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
 
    
    @Test
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
        main.addOptions("-subexpressions","-show");
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


}

