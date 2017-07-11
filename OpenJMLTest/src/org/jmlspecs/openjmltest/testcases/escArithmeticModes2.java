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
        String[] options = {"-escBV=false,-minQuant","-escBV=false,-no-minQuant","-escBV=true,-minQuant","-escBV=true,-no-minQuant"};
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
                +"}\n"
              );
    }

    @Test
    public void testModJavaZ() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecSafeMath public class TestJava { \n"
                +"  public long m() {\n"
                +"    int k = 15 ;\n" 
                +"    int j = 5;\n" 
                +"    int m = 0;\n" 
                +"    int qq = 3;\n" 
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
                +"}\n"
              );
    }

    @Test
    public void testModJavaB() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Very long - skip for now
        main.addOptions("-show","-method=ma","-subexpressions");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecJavaMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires j != -1 || i != 0x80000000;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int q = i/j; int r = i%j; int k = q * j + r;\n"
                +"    //@ assert (\\lbl KK (\\lbl Q q) * (\\lbl J j) + (\\lbl R r)) == (\\lbl I i); \n"
                +"    //@ assert (\\lbl K k) == (\\lbl I i); \n"
                +"    //@ assert (\\lbl QQ (i/j)) * j + (\\lbl RR (i%j)) == i; \n"
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
                +"}\n"
              );
    }

    @Test
    public void testModSafeZ() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  public void m() {\n"
                +"    int k = 15 ;\n" 
                +"    int j = 5;\n" 
                +"    int m = 0;\n" 
                +"    int qq = 3;\n" 
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
                +"}\n"
              );
    }


    @Test
    public void testModSafeB() {
       Assume.assumeTrue(!options.contains("-escBV=true")); // Very long - skip for now
       helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires j != -1 || i != 0x80000000;\n"
                +"  public void ma(int i, int j) {\n"
                +"    //@ assert (\\lbl I i) + 0*(\\lbl J j) == i; \n" // Just to print i and j
                +"    int q = (i/j) ;\n"
                +"    //@ assert (\\lbl Q q) * 0 == 0; \n" // Just to print q
                +"    int k = q * j + (i%j);\n"
                +"    //@ assert (\\lbl K k) == (\\lbl I i); \n"
                +"    //@ assert (\\lbl D ((\\lbl I i)/(\\lbl J j)))*j + (\\lbl M (i%j)) == i; \n"  // not OK for i = MIN && j = -1
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModSafeBB() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Very long - skip for now

        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int k = (i/j) * j + (i%j);\n"
                +"    //@ assert k == i; \n"
                +"    //@ assert (i/j) * j + (i%j) == i; \n"
                +"  }\n"
                +"}\n"
                ,anyorder(seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma:  int multiply overflow",19)
                ,seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma:  overflow in int divide",15)
                )
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
                +"}\n"
              );
    }
    
    @Test
    public void testModMathZ() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  public void m() {\n"
                +"    int k = 15 ;\n" 
                +"    int j = 5;\n" 
                +"    int m = 0;\n" 
                +"    int qq = 3;\n" 
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
                +"}\n"
              );
    }

    @Test
    public void testModMathB() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int k = (i/j) * j + (i%j);\n"
                +"    //@ assert k == i; \n"
                +"    //@ assert (i/j) * j + (i%j) == i; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModEqual() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int k = (i%j);\n"
                +"    int m = (i/j);\n"
                +"    //@ assert (i%j) == (\\lbl K k); \n"  // OK
                +"    //@ assert (\\lbl D ((\\lbl I i)/(\\lbl J j))) == (\\lbl M m); \n"  // mnot OK for i = MIN && j = -1
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:7: warning: Label K has value 0",31
                ,"/tt/TestJava.java:8: warning: Label I has value ( - 2147483648 )",31
                ,"/tt/TestJava.java:8: warning: Label J has value ( - 1 )",42
                ,"/tt/TestJava.java:8: warning: Label D has value 2147483648",22
                ,"/tt/TestJava.java:8: warning: Label M has value ( - 2147483648 )",58
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method ma",9
                
              );
    }

    @Test
    public void testModEqualB() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i != 0x80000000 || j != -1;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int k = (i%j);\n"
                +"    int m = (i/j);\n"
                +"    //@ assert (i%j) == (\\lbl K k); \n"  // OK
                +"    //@ assert (i/j) == (\\lbl M m); \n"  // OK for i = MIN && j = -1
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModEqualLong() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(long i, long j) {\n"
                +"    long k = (i%j);\n"
                +"    long m = (i/j);\n"
                +"    //@ assert (i%j) == (\\lbl K k); \n"  // OK
                +"    //@ assert (\\lbl D ((\\lbl I i)/(\\lbl J j))) == (\\lbl M m); \n"  // mnot OK for i = MIN && j = -1
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:7: warning: Label K has value 0",31
                ,"/tt/TestJava.java:8: warning: Label I has value ( - 9223372036854775808 )",31
                ,"/tt/TestJava.java:8: warning: Label J has value ( - 1 )",42
                ,"/tt/TestJava.java:8: warning: Label D has value 9223372036854775808",22
                ,"/tt/TestJava.java:8: warning: Label M has value ( - 9223372036854775808 )",58
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method ma",9
                
              );
    }

    @Test
    public void testModEqualLongB() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i != 0x8000000000000000L || j != -1;\n"
                +"  public void ma(long i, long j) {\n"
                +"    long k = (i%j);\n"
                +"    long m = (i/j);\n"
                +"    //@ assert (i%j) == (\\lbl K k); \n"  // OK
                +"    //@ assert (i/j) == (\\lbl M m); \n"  // OK for i = MIN && j = -1
                +"  }\n"
                +"}\n"
              );
    }


}

