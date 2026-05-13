package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;


@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escArithmeticModes extends EscBase {

    static boolean runLongArithmetic = runLongTests || System.getProperty("RUNLONGARITH") != null;

    static {
        if (runLongTests && !runLongArithmetic) System.out.println("Skipping long tests in escArithmeticModes");
    }

    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        addOptions("--nullable-by-default"); // Because the tests were written this way
        //addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
    
    public boolean bvCheck() {
    	return options == null || !options.contains("--esc-bv=true"); // FIXME - options is not used, I think
    }
 
    
    @Test @Ignore // Times out in BV mode
    public void testNegNeg() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i >= 0;
                  //@ ensures \\result == i;
                  public int m(int i) {
                    int k = -(-i);
                    return k;
                  }
                }
                """
              );
    }

    @Test
    public void testNegJavaInt() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ ensures i != 0x80000000 ==> \\safe_math(\\result + i) == 0;
                  //@ ensures i == 0x80000000 ==> \\result == i;
                  /*@ code_java_math spec_bigint_math */ public int m(int i) {
                    int k = -i;
                    return k;
                  }
                }
                """
              );
    }

    @Test
    public void testNegJavaLong() {  // Takes about 5 min in BV mode
        Assume.assumeTrue(runLongArithmetic || bvCheck());
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ ensures i != 0x8000000000000000L ==> \\safe_math(\\result + i) == 0;
                  //@ ensures i == 0x8000000000000000L ==> \\result == i;
                  /*@ code_java_math */ public long ml(long i) {
                    long k = -i;
                    return k;
                  }
                }
                """
              );
    }

    @Test
    public void testNegSafe() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath @SpecBigintMath public class TestJava {
                  //@ ensures i != 0x80000000 ==> \\safe_math(\\result + i) == 0;
                  //@ ensures i == 0x80000000 ==> \\result == i;
                  public int m(int i) {
                    int k = -i;
                    return k;
                  }
                  //@ ensures i != 0x8000000000000000L ==> \\safe_math(\\result + i) == 0;
                  //@ ensures i == 0x8000000000000000L ==> \\result == i;
                  public long ml(long i) {
                    long k = -i;
                    return k;
                  }
                  //@ ensures \\safe_math(\\result + i) == 0;
                  public int mm(short i) {
                    int k = -i;
                    return k;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method m: int negation",13
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method ml: long negation",14
              );
    }

    @Test
    public void testNegMath() { // FIXME - review this one
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath @SpecBigintMath public class TestJava {
                  //@ ensures \\safe_math(\\result + i) == 0;
                  public int m(int i) {
                    int k = -i;
                    return k;
                  }
                  //@ ensures \\safe_math(\\result + i) == 0;
                  public long ml(long i) {
                    long k = -i;
                    return k;
                  }
                  //@ ensures \\safe_math(\\result + i) == 0;
                  public int ms(short i) {
                    int k = -i;
                    return k;
                  }
                }
                """
//                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m: int overflow",13
//                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method ml: long overflow",14
              );
    }

    @Test
    public void testSumSafe1() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath public class TestJava {
                  public int m(int i) {
                    int k = i + i;
                    return k;
                  }
                }
                """
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method m: underflow in int sum",15)
                         ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method m: overflow in int sum",15))
              );
    }

    @Test
    public void testSumSafe2() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath public class TestJava {
                  public int ma(int i) {
                    //@ assume i <= 0x3FFFFFFF;
                    int k = i + i;
                    return k;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma: underflow in int sum",15
              );
    }

    @Test
    public void testSumSafe3() {
        Assume.assumeTrue(runLongArithmetic || bvCheck());
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath public class TestJava {
                  public int mb(int i) {
                    //@ assume i >= (int)(0xC0000000);
                    int k = i + i;
                    return k;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method mb: overflow in int sum",15
              );
    }

    @Test @Ignore // FIXME - TIME OUT
    public void testSumSafe4() {
        Assume.assumeTrue(runLongArithmetic || bvCheck());
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath public class TestJava {
                  public int mc(int i) {
                    //@ assume i <= 0x3FFFFFFF;
                    //@ assume i >= (int)(0xC0000000);
                    int k = i + i;
                    return k;
                  }
                  public int mm(int i, int j) {
                    //@ assume (i < 0) != (j < 0);
                    int k = i + j;
                    return k;
                  }
                }
                """
              );
    }

    @Test
    public void testSumJava() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath public class TestJava {
                  public int m(int i) {
                    int k = i + i;
                    return k;
                  }
                  public int mb(int i) {
                    //@ assume i >= 0;
                    int k = i + i;
                    //@ check k >= 0;
                    return k;
                  }
                  public int mm(int i, int j) {
                    int k = i + j;
                    return k;
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method mb",9
              );
    }

    @Test
    public void testSumMath() { // FIXME _ review this one
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath public class TestJava {
                  public int m(int i) {
                    int k = i + i;
                    return k;
                  }
                  public long mb(int i) {
                    //@ assume i >= 0;
                    long k = i + i;
                    //@ check k >= 0;
                    return k;
                  }
                  public int mm(int i, int j) {
                    int k = i + j;
                    return k;
                  }
                }
                """
//                ,seq(
//                anyorder(
//                 seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int overflow",13)
//                ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int underflow",13)
//                ),anyorder(
//                 seq("/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method mb:  int overflow",18)
//                ,seq("/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method mb:  int underflow",18)
//                ))
              );
    }

    @Test @Ignore // FIXME - still have to sort out how assignments are handled in Math mode
    public void testSumMathArg() {
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath public class TestJava {
                  @SkipEsc public long mb(int i) {
                    //@ assume i >= 0;
                    long k = i + i;
                    //@ check k >= 0;
                    return k;
                  }
                  public long mq(int i, int j) {
                    long k = mb(i + j);
                    return k;
                  }
                }
                """
                ,seq(
                anyorder(
                 seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int overflow",13)
                ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int underflow",13)
//                ),anyorder(
//                 seq("/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method mb:  int overflow",18)
//                ,seq("/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method mb:  int underflow",18)
                ))
              );
    }

    @Test
    public void testSumMathB() { // FIXME _ review this one
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath public class TestJava {
                  public int m(int i) {
                    int k = i + i;
                    return k;
                  }
                  public int mb(int i) {
                    //@ assume i >= 0;
                    int k = (int)(i + i);
                    //@ check k >= 0;
                    return k;
                  }
                }
                """
//                ,anyorder(
//                  seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int overflow",13)
//                 ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int underflow",13)
//                 )
//                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method mb:  int overflow",18
              );
    }

    @Test
    public void testDivJava() {
        Assume.assumeTrue(runLongArithmetic);
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath public class TestJava { //@ requires j !=0 ;
                  public int m(int i, int j) {
                    int k = i/j;
                    return k;
                  }
                }
                """
              );
    }

    @Test
    public void testDivSafe() {
        Assume.assumeTrue(runLongArithmetic);
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath public class TestJava {
                  //@ requires j !=0;
                  public int m(int i, int j) {
                    int k = i/j;
                    return k;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method m: overflow in int divide",14
              );
    }

    @Test
    public void testDivMath() {// FIXME _ review this one
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath public class TestJava {
                  //@ requires j !=0;
                  public long m(int i, int j) {
                    long k = i/j;
                    return k;
                  }
                }
                """
              );
    }
    
    // FIXME - need to test long versions of Mult and perhaps everything else

    @Test
    public void testMultSafe() {
        Assume.assumeTrue(runLongArithmetic || bvCheck());
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath @SpecSafeMath public class TestJava {
                  public int m(int i) {
                    int k = i * i;
                    return k;
                  }
                  public int ma(int i) {
                    //@ assume i <= 30000 && i >= -30000;
                    int k = i * i;
                    return k;
                  }
                  //@ requires i == 70000;
                  //@ ensures \\result == 605032704;
                  public int mc(int i) {
                    int k = i * i;
                    return k;
                  }
                  //@ requires i == 30000;
                  //@ ensures \\result == 900000000L;
                  public long me(int i) {
                    long k = i * i;
                    return k;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method m: int multiply out of range",15
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method mc: int multiply out of range",15
              );
    }

    @Test
    public void testMultJava() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecSafeMath public class TestJava {
                  public long m(int i) {
                    long k = i * i;
                    return k;
                  }
                  public int ma(int i) {
                    //@ assume i <= 30000 && i >= -30000;
                    int k = i * i;
                    return k;
                  }
                  //@ requires i == 70000;
                  //@ ensures \\result == 605032704L;
                  public int mc(int i) {
                    int k = i * i;
                    return k;
                  }
                  //@ requires i == 70000;
                  //@ ensures \\result == -605032704L;
                  public int md(int i) {
                    int k = -i * i;
                    return k;
                  }
                  //@ requires i == 70000;
                  //@ ensures \\result == -605032704L;
                  public long mdd(int i) {
                    long k = -i * i;
                    return k;
                  }
                  //@ requires i == 30000;
                  //@ ensures \\result == 900000000L;
                  public long me(int i) {
                    long k = i * i;
                    return k;
                  }
                }
                """
              );
    }

    @Test
    public void testMultMath() {// FIXME _ review this one
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath public class TestJava {
                  public long m(int i) {
                    long k = i * i;
                    return k;
                  }
                  public int ma(int i) {
                    //@ assume i <= 30000 && i >= -30000;
                    int k = i * i;
                    return k;
                  }
                  //@ requires i == 70000;
                  //@ ensures \\result == 4900000000L;
                  public int mc(int i) {
                    int k = i * i;
                    return k;
                  }
                  //@ requires i == 70000;
                  //@ ensures \\result == -4900000000L;
                  public int md(int i) {
                    int k = -i * i;
                    return k;
                  }
                  //@ requires i == 70000;
                  //@ ensures \\result == 4900000000L;
                  public long me(int i) {
                    long k = i * i;
                    return k;
                  }
                }
                """
//                ,anyorder(seq("/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method mc:  int overflow",13)
//                ,seq("/tt/TestJava.java:21: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method md:  int underflow",21)
//                )
              );
    }
}

