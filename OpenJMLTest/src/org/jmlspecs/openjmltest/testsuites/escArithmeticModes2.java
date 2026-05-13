package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;


@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escArithmeticModes2 extends EscBase {

    static boolean runLongArithmetic = runLongTests || System.getProperty("RUNLONGARITH") != null;
    
    static {
        if (runLongTests && !runLongArithmetic) System.out.println("Skipping long tests in escArithmeticModes2");
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
    	return options == null || !(options.contains("-escBV=true")||options.contains("-escBV=auto"));
    }
 
    // Checks the value and sign of int division and mod
    @Test
    public void testModJava() {
        Assume.assumeTrue(runLongArithmetic);
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecSafeMath public class TestJava {
                  public long m() {
                    int k = 7 ;
                    int j = 3;
                    int m = 1;
                    int qq = 2;
                    int i = k % j;
                    int q = k / j;
                    //@ check i == m && q == qq ;
                    //@ check (k%j) == m && (k/j) == qq;
                    i = (-k) % j;
                    q = (-k) / j;
                    //@ check i == -m && q == -qq;
                    //@ check ((-k)%j) == -m && ((-k)/j) == -qq;
                    i = k % -j;
                    q = k / -j;
                    //@ check i == m && q == -qq;
                    //@ check (k%-j) == m && (k/-j) == -qq;
                    i = -k % -j;
                    q = -k / -j;
                    //@ check i == -m && q == qq;
                    //@ check (-k%-j) == -m && ((-k)/-j) == qq;
                    return k;
                  }
                }
                """
              );
    }

    // Checks the value and sign of int division and mod
    @Test
    public void testModJavaZ() {
        Assume.assumeTrue(runLongArithmetic);
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecSafeMath public class TestJava {
                  public long m() {
                    int k = 15 ;
                    int j = 5;
                    int m = 0;
                    int qq = 3;
                    int i = k % j;
                    int q = k / j;
                    //@ check i == m && q == qq ;
                    //@ check (k%j) == m && (k/j) == qq;
                    i = (-k) % j;
                    q = (-k) / j;
                    //@ check i == -m && q == -qq;
                    //@ check ((-k)%j) == -m && ((-k)/j) == -qq;
                    i = k % -j;
                    q = k / -j;
                    //@ check i == m && q == -qq;
                    //@ check (k%-j) == m && (k/-j) == -qq;
                    i = -k % -j;
                    q = -k / -j;
                    //@ check i == -m && q == qq;
                    //@ check (-k%-j) == -m && ((-k)/-j) == qq;
                    return k;
                  }
                }
                """
              );
    }

    // Checks the value and sign of int division and mod
    @Test
    public void testModJava3() {
        Assume.assumeTrue(runLongArithmetic);
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecSafeMath public class TestJava {
                  public long m() {
                    int k = - 2147483648 ;
                    int j = - 1073740802;
                    int m = - 2044;
                    int qq = 2;
                    int i = k % j;
                    int q = k / j;
                    //@ check i == m && q == qq ;
                    //@ check (k%j) == m && (k/j) == qq;
                    return k;
                  }
                }
                """
              );
    }

    @Test
    public void testModJavaB() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(bvCheck());
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecJavaMath public class TestJava {
                  //@ requires j != 0;
                  //@ requires j != -1 || i != 0x80000000;
                  public void ma(int i, int j) {
                    int q = i/j; int r = i%j; int k = q * j + r;
                    //@ show i, j, q, r, k;
                    //@ check (\\lbl KK (q * j + r)) == i;
                    //@ check k == i;
                    //@ check (\\lbl QQ (i/j)) * j + (\\lbl RR (i%j)) == i;
                  }
                }
                """
              );
    }

    @Test
    public void testModSafe() {
        Assume.assumeTrue(runLongArithmetic && bvCheck());
        addOptions("--solver-seed=142");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath @SpecSafeMath public class TestJava {
                  public void m() {
                    int k = 7 ;
                    int j = 3;
                    int m = 1;
                    int qq = 2;
                    int i = k % j;
                    int q = k / j;
                    //@ check i == m && q == qq ;
                    //@ check (k%j) == m && (k/j) == qq;
                    i = (-k) % j;
                    q = (-k) / j;
                    //@ check i == -m && q == -qq;
                    //@ check ((-k)%j) == -m && ((-k)/j) == -qq;
                    i = k % -j;
                    q = k / -j;
                    //@ check i == m && q == -qq;
                    //@ check (k%-j) == m && (k/-j) == -qq;
                    i = -k % -j;
                    q = -k / -j;
                    //@ check i == -m && q == qq;
                    //@ check (-k%-j) == -m && ((-k)/-j) == qq;
                  }
                }
                """
              );
    }

    @Ignore // FIXME - times out
    @Test
    public void testModSafeZ() {
        Assume.assumeTrue(runLongArithmetic && bvCheck());
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath @SpecSafeMath public class TestJava {
                  public void m() {
                    int k = 15 ;
                    int j = 5;
                    int m = 0;
                    int qq = 3;
                    int i = k % j;
                    int q = k / j;
                    //@ check i == m && q == qq ;
                    //@ check (k%j) == m && (k/j) == qq;
                    i = (-k) % j;
                    q = (-k) / j;
                    //@ check i == -m && q == -qq;
                    //@ check ((-k)%j) == -m && ((-k)/j) == -qq;
                    i = k % -j;
                    q = k / -j;
                    //@ check i == m && q == -qq;
                    //@ check (k%-j) == m && (k/-j) == -qq;
                    i = -k % -j;
                    q = -k / -j;
                    //@ check i == -m && q == qq;
                    //@ check (-k%-j) == -m && ((-k)/-j) == qq;
                  }
                }
                """
              );
    }


    @Ignore // FIXME - non-linear arithmetic has bad models
    @Test
    public void testModSafeB() {
        //Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(bvCheck()); // Very long - skip for now
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath @SpecSafeMath public class TestJava {
                  //@ requires j != 0 && i > 0 && j > 0;
                  //@ requires j != -1 || i != 0x80000000;
                  public void ma(int i, int j) {
                    //@ show i, j;
                    int q = (i/j) ;
                    int m = (i%j) ;
                    //@ show q, m;
                    int k = q * j + m;
                    //@ check (\\lbl K k) == (\\lbl I i);
                    //@ check (\\lbl SUM (\\lbl PROD (\\lbl D ((\\lbl I i)/(\\lbl J j)))*(\\lbl JJ j)) + (\\lbl M (i%j))) == i;
                  }
                }
                """
              );
    }

    @Test
    public void testModSafeBB() {
        Assume.assumeTrue(bvCheck()); // Very long - skip for now - TODO

        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath @SpecSafeMath public class TestJava {
                  //@ requires j != 0;
                  public void ma(int i, int j) {
                    int k = (i/j) * j + (i%j);
                    //@ check k == i;
                    //@ check (i/j) * j + (i%j) == i;
                  }
                }
                """ // FIXME - not sure why the multiply overflow is sometimes not reported
                ,anyorder(
                   seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma: overflow in int divide",15)
                  ,seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma: int multiply out of range",19)
                  ,seq("/tt/TestJava.java:7: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma: overflow in int divide",17)
                  ,seq("/tt/TestJava.java:7: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma: int multiply out of range",21)
                  ,optional("/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method ma",9)
                )
              );
    }

    @Test
    public void testModMath() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath @SpecBigintMath public class TestJava {
                  public void m() {
                    int k = 7 ;
                    int j = 3;
                    int m = 1;
                    int qq = 2;
                    int i = k % j;
                    int q = k / j;
                    //@ check i == m && q == qq ;
                    //@ check (k%j) == m && (k/j) == qq;
                    i = (-k) % j;
                    q = (-k) / j;
                    //@ check i == -m && q == -qq;
                    //@ check ((-k)%j) == -m && ((-k)/j) == -qq;
                    i = k % -j;
                    q = k / -j;
                    //@ check i == m && q == -qq;
                    //@ check (k%-j) == m && (k/-j) == -qq;
                    i = -k % -j;
                    q = -k / -j;
                    //@ check i == -m && q == qq;
                    //@ check (-k%-j) == -m && ((-k)/-j) == qq;
                  }
                }
                """
              );
    }

    @Test @Ignore // TIMES OUT
    public void testModMathZ() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath @SpecBigintMath public class TestJava {
                  public void m() {
                    int k = 15 ;
                    int j = 5;
                    int m = 0;
                    int qq = 3;
                    int i = k % j;
                    int q = k / j;
                    //@ check i == m && q == qq ;
                    //@ check (k%j) == m && (k/j) == qq;
                    i = (-k) % j;
                    q = (-k) / j;
                    //@ check i == -m && q == -qq;
                    //@ check ((-k)%j) == -m && ((-k)/j) == -qq;
                    i = k % -j;
                    q = k / -j;
                    //@ check i == m && q == -qq;
                    //@ check (k%-j) == m && (k/-j) == -qq;
                    i = -k % -j;
                    q = -k / -j;
                    //@ check i == -m && q == qq;
                    //@ check (-k%-j) == -m && ((-k)/-j) == qq;
                  }
                }
                """
              );
    }

    @Test
    public void testModMathB() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  public void ma(int i, int j) {
                    int q,m; int k = (q=i/j) * j + (m=i%j);
                    //@ show i,j,k,q,m,i/j,i%j; check k == i;
                    //@ check (i/j) * j + (i%j) == i;
                  }
                }
                """
              );
    }

    @Test
    public void testModEqual() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  public void ma(int i, int j) {
                    int k = (i%j);
                    int m = (i/j);
                    //@ check (i%j) == (\\lbl K k);
                    //@ check (\\lbl D ((\\lbl I i)/(\\lbl J j))) == (\\lbl M m);
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: Label K has value 0",30
                ,"/tt/TestJava.java:8: verify: Label I has value ( - 2147483648 )",30
                ,"/tt/TestJava.java:8: verify: Label J has value ( - 1 )",41
                ,"/tt/TestJava.java:8: verify: Label D has value 2147483648",21
                ,"/tt/TestJava.java:8: verify: Label M has value ( - 2147483648 )",57
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method ma",9
              );
    }

    @Test
    public void testModEqualB() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  //@ requires i != 0x80000000 || j != -1;
                  public void ma(int i, int j) {
                    int k = (i%j);
                    int m = (i/j);
                    //@ check (i%j) == (\\lbl K k);
                    //@ check (i/j) == (\\lbl M m);
                  }
                }
                """
              );
    }

    @Test
    public void testModEqualLong() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  public void ma(long i, long j) {
                    long k = (i%j);
                    long m = (i/j);
                    //@ check (i%j) == (\\lbl K k);
                    //@ check (\\lbl D ((\\lbl I i)/(\\lbl J j))) == (\\lbl M m);
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: Label K has value 0",30
                ,"/tt/TestJava.java:8: verify: Label I has value ( - 9223372036854775808 )",30
                ,"/tt/TestJava.java:8: verify: Label J has value ( - 1 )",41
                ,"/tt/TestJava.java:8: verify: Label D has value 9223372036854775808",21
                ,"/tt/TestJava.java:8: verify: Label M has value ( - 9223372036854775808 )",57
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method ma",9
              );
    }

    @Test
    public void testModEqualLongB() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  //@ requires i != 0x8000000000000000L || j != -1;
                  public void ma(long i, long j) {
                    long k = (i%j);
                    long m = (i/j);
                    //@ check (i%j) == (\\lbl K k);
                    //@ check (i/j) == (\\lbl M m);
                  }
                }
                """
              );
    }

    @Ignore // FIXME
    @Test // Tests int multiplication in bigint mode
    public void testMult() {
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  //@ requires i * j <= Integer.MAX_VALUE && i*j >= Integer.MIN_VALUE;
                  public void ma(int i, int j) {
                    //@ show i,j,i*j,(i*j)/j;
                    //@ check (i*j)/j == i;
                    boolean b =  (i*j)/j == i;
                    //@ check b;
                  }
                }
                """
              );
    }

    @Ignore // FIXME long running
    @Test // Tests long multiplication in bigint mode
    public void testMultLong() {
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  //@ requires i * j <= Long.MAX_VALUE && i*j >= Long.MIN_VALUE;
                  public void ma(long i, long j) {
                    //@ show i,j,i*j,(i*j)/j;
                    //@ check (i*j)/j == i;
                    boolean b =  (i*j)/j == i;
                    //@ check b;
                  }
                }
                """
              );
    }

    @Ignore // FIXME - long running
    @Test // Tests int multiplication in java mode
    public void testMultJava() {
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  //@ requires i * j <= Integer.MAX_VALUE && i*j >= Integer.MIN_VALUE;
                  public void ma(int i, int j) {
                    //@ show i,j,i*j,(i*j)/j;
                    //@ check (i*j)/j == i;
                    boolean b =  (i*j)/j == i;
                    //@ check b;
                  }
                }
                """
              );
    }

    @Ignore // FIXME -- long running
    @Test // Tests long multiplication in java mode
    public void testMultJavaLong() {
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  //@ requires i * j <= Long.MAX_VALUE && i*j >= Long.MIN_VALUE;
                  public void ma(long i, long j) {
                    //@ show i,j,i*j,(i*j)/j;
                    //@ check (i*j)/j == i;
                    boolean b =  (i*j)/j == i;
                    //@ check b;
                  }
                }
                """
              );
    }

    @Ignore // FIXME - long running
    @Test // Tests int multiplication in safe mode
    public void testMultSafe() {
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  //@ requires i * j <= Integer.MAX_VALUE && i*j >= Integer.MIN_VALUE;
                  public void ma(int i, int j) {
                    //@ show i,j,i*j,(i*j)/j;
                    //@ check (i*j)/j == i;
                    boolean b =  (i*j)/j == i;
                    //@ check b;
                  }
                }
                """
              );
    }

    @Ignore // FIXME - long
    @Test // Tests long multiplication in safe mode
    public void testMultSafeLong() {
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  //@ requires i * j <= Long.MAX_VALUE && i*j >= Long.MIN_VALUE;
                  public void ma(long i, long j) {
                    //@ show i,j,i*j,(i*j)/j;
                    //@ check (i*j)/j == i;
                    boolean b =  (i*j)/j == i;
                    //@ check b;
                  }
                }
                """
              );
    }

    @Ignore // FIXME - long running
    @Test  // Tests that div and mod give correct answers, if they do not overflow, in bigint mode
    public void testDiv() {
        Assume.assumeTrue(bvCheck()); // Cannot have BV and Math mode
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeBigintMath @SpecBigintMath public class TestJava {
                  //@ requires j != 0;
                  public void ma(int i, int j) {
                    int q = i/j; //@ ghost int qq = i/j;
                    int m = i%j;
                    //@ show i,j,q,qq,m,i/j,i%j,j*q,j*(q+1),j*(q-1),j*q+m;
                    if (i >= 0 && j >= 0) { /*@ check q >= 0; check i >= j*q; check i-j < j*(q+1); check m >= 0 && m < j; check i == (j*q) + m; */ }
                    if (i >= 0 && j < 0) { /*@ check q <= 0; check i >= j*q; check i < j*(q-1);  check m >= 0 && m < -j; check i == (j*q) + m; */ }
                    if (i < 0 && j >= 0) { /*@ check q <= 0; check i <= j*q; check i > j*(q-1); check m <= 0 && m > -j; check i == (j*q) + m; */ }
                    if (i < 0 && j < 0) { /*@ check q >= 0; check i <= j*q; check i > j*(q+1); check m <= 0 && m > j; check i == (j*q) + m; */ }
                  }
                }
                """
              );
    }

    @Ignore // FIXME -- long running
    @Test  // Tests that div and mod give correct answers, if they do not overflow, in java mode
    public void testDivJava() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecSafeMath @Options("-escMaxWarnings=1") public class TestJava {
                  //@ requires j != 0;
                  //@ requires i != Integer.MIN_VALUE || j != -1;
                  public void ma(int i, int j) {
                    int q = i/j;
                    int m = i%j;
                    //@ show i,j,q,m,j*q,j*(q+1),j*(q-1),j*q+m;
                    if (i >= 0 && j >= 0) { /*@ check q >= 0; check i >= j*q; check i < j*(q+1); check m >= 0 && m < j; check i == (j*q) + m; */ }
                    if (i >= 0 && j < 0) { /*@ check q <= 0; check i >= j*q; check i < j*(q-1);  check m >= 0 && m < -j; check i == (j*q) + m; */ }
                    if (i < 0 && j >= 0) { /*@ check q <= 0; check i <= j*q; check i > j*(q-1); check m <= 0 && m < -j; check i == (j*q) + m; */ }
                    if (i < 0 && j < 0) { /*@ check q >= 0; check i <= j*q; check i > j*(q+1); check m <= 0 && m > j; check i == (j*q) + m; */ }
                  }
                }
                """
              );
    }

    @Ignore // FIXME -- long running
    @Test  // Tests that div and mod give correct answers, if they do not overflow, in safe mode
    public void testDivSafe() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @CodeSafeMath @SpecSafeMath @Options("-escMaxWarnings=1") public class TestJava {
                  //@ requires j != 0;
                  //@ requires i != Integer.MIN_VALUE || j != -1;
                  public void ma(int i, int j) {
                    //@ show i,j;
                    int q = i/j;
                    int m = i%j;
                    //@ show q,m,j*q,j*(q+1),j*(q-1),j*q+m;
                    if (i >= 0 && j >= 0) { /*@ check q >= 0; check i >= j*q; check m >= 0 && m < j; check i == (j*q) + m; */ }
                    if (i >= 0 && j < 0) { /*@ check q <= 0; check i >= j*q;  check m >= 0 && m < -j; check i == (j*q) + m; */ }
                    if (i < 0 && j >= 0) { /*@ check q <= 0; check i <= j*q; check m <= 0 && m < -j; check i == (j*q) + m; */ }
                    if (i < 0 && j < 0) { /*@ check q >= 0; check i <= j*q; check m <= 0 && m > j; check i == (j*q) + m; */ }
                  }
                }
                """
              );
    }
    


}

