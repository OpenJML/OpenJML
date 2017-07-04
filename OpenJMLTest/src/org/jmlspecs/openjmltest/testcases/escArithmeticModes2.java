package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;


@RunWith(ParameterizedWithNames.class)
public class escArithmeticModes2 extends EscBase {

    
    @Parameters
    static public Collection<String[]> parameters() {
        String[] options = {"-escBV=true,-minQuant","-escBV=true,-no-minQuant","-escBV=false,-minQuant","-escBV=false,-no-minQuant"};
        return optionsAndSolvers(options,solvers);
    }


    public escArithmeticModes2(String options, String solver) {
        super(options,solver);
    }
    
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
 

    @Test
    public void testModJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecSafeMath public class TestJava { \n"
                +"  public long m() {\n"
                +"    int k = 7 ;\n" 
                +"    int j = 3;\n" 
                +"    int m = 1;\n" 
                +"    int qq = 2;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"    return k; \n"
                +"  }\n"
                +"  //@ requires j != 0 && j < 100 && j > -100 && i < 100 && i > -100;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int k = (i/j) * j + (i%j);\n"
                +"    //@ assert k == 0; \n"
                +"    //@ assert (i/j) * j + (i%j) == 0; \n"    // Line 30
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  public void m() {\n"
                +"    int k = 7 ;\n" 
                +"    int j = 3;\n" 
                +"    int m = 1;\n" 
                +"    int qq = 2;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"  }\n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int k = (i/j) * j + (i%j);\n"
                +"    //@ assert k == 0; \n"
                +"    //@ assert (i/j) * j + (i%j) == 0; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModMath() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  public void m() {\n"
                +"    int k = 7 ;\n" 
                +"    int j = 3;\n" 
                +"    int m = 1;\n" 
                +"    int qq = 2;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"  }\n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int k = (i/j) * j + (i%j);\n"
                +"    //@ assert k == 0; \n"
                +"    //@ assert (i/j) * j + (i%j) == 0; \n"
                +"  }\n"
                +"}\n"
              );
    }

}

