package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;

import org.junit.*;

/** These tests exercise the RAC checking.  They compile a test class
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racArithmeticModes extends RacBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("-jmltesting");
    }

    @Override
    public void tearDown() throws Exception {
        testspecpath1 = "$A"+z+"$B";
    }


    @Test public void testNegJava() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = -250000;
                    int k = -i;
                    System.out.println((k==i) + " " + (k+i) + " END");
                    i = Integer.MIN_VALUE;
                    k = -i;
                    System.out.println((k==i) + " END");
                  }
                }
                """
                ,"false 0 END"
                ,"true END"
                );

    }

    @Test public void testNegJavaLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = -250000;
                    long k = -i;
                    System.out.println((k==i) + " " + (k+i) + " END");
                    i = Long.MIN_VALUE;
                    k = -i;
                    System.out.println((k==i) + " END");
                  }
                }
                """
                ,"false 0 END"
                ,"true END"
                );

    }

    @Test public void testNegSafe() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = -250000;
                    int k = -i;
                    System.out.println((k==i) + " " + (k+i) + " END");
                    i = Integer.MIN_VALUE;
                    k = -i;
                    System.out.println((k==i) + " END");
                  }
                }
                """
                ,"false 0 END"
                ,"/tt/TestJava.java:10: JML result of numeric operation is out of range of the target type"
                ,"true END"
                );

    }

    @Test public void testNegSafeLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = -250000;
                    long k = -i;
                    System.out.println((k==i) + " " + (k+i) + " END");
                    i = Long.MIN_VALUE;
                    k = -i;
                    System.out.println((k==i) + " END");
                  }
                }
                """
                ,"false 0 END"
                ,"/tt/TestJava.java:10: JML result of numeric operation is out of range of the target type"
                ,"true END"
                );

    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testNegMath() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    int j = Integer.MAX_VALUE;
                    long k = -j;
                    System.out.println(k + " END");
                    int i = Integer.MIN_VALUE;
                    long kk = -i;
                    System.out.println(kk + " END");
                  }
                }
                """
                ,"-2147483647 END"
                ,"2147483648 END"
                );
    }

    // FIXME - in bigint mode, should all integer decls be bigint instead?
    @Ignore // No CodeBigintMath as yet
    @Test public void testNegMath2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    int j = Integer.MAX_VALUE;
                    int k = -j;
                    System.out.println(k + " END");
                    int i = Integer.MIN_VALUE;
                    int kk = -i;
                    System.out.println(kk + " END");
                  }
                }
                """
                ,"-2147483647 END"
                ,"verify: JML argument to numeric cast is out of range of the target type"
                ,"-2147483648 END"
                );
    }

    // FIXME - in bigint mode, should all integer decls be bigint instead?
    @Ignore // No CodeBigintMath as yet
    @Test public void testNegMathLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    long j = Long.MAX_VALUE;
                    long k = -j;
                    System.out.println(k + " END");
                    long i = Long.MIN_VALUE;
                    long kk = -i;
                    System.out.println(kk + " END");
                  }
                }
                """
                ,"-9223372036854775807 END"
                ,"verify: JML argument to numeric cast is out of range of the target type"
                ,"-9223372036854775808 END"
                );
    }

    @Test public void testCompJava() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MIN_VALUE;
                    int k = ~i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 2147483647"
                );
    }

    @Test public void testCompSafe() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MIN_VALUE;
                    int k = ~i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 2147483647"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testCompMath() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MIN_VALUE;
                    int k = ~i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 2147483647"
                );
    }


    @Test public void testSumJava() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MAX_VALUE;
                    int k = i + i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END -2"
                );
    }

    @Test public void testSumSafe() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MAX_VALUE;
                    int k = i + i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"/tt/TestJava.java:7: JML result of numeric operation is out of range of the target type"
                ,"END -2"
                );
    }

    @Test public void testSumJavaLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = Long.MAX_VALUE;
                    long k = i + i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END -2"
                );
    }

    @Test public void testSumSafeLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = Long.MAX_VALUE;
                    long k = i + i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"/tt/TestJava.java:7: JML result of numeric operation is out of range of the target type"
                ,"END -2"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testSumMath() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MAX_VALUE;
                    long k = i + i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 4294967294"
                );
    }

    // FIXME - still have to sort out how assignments are handled in Math mode
    @Ignore // No CodeBigintMath as yet
    @Test public void testSumMathCast() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MAX_VALUE;
                    int k = i + i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"/tt/TestJava.java:7: JML argument to numeric cast is out of range of the target type"
                ,"END -2"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testSumMathArg() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MAX_VALUE;
                    mm(i+i);
                  }
                  static void mm(int k) { System.out.println("END " + k); }
                }
                """
                ,"/tt/TestJava.java:7: JML argument to numeric cast is out of range of the target type"
                ,"END -2"
                );
    }


    @Test public void testDiffJava() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MAX_VALUE;
                    int k = i - Integer.MIN_VALUE;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END -1"
                );
    }

    @Test public void testDiffSafe() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MAX_VALUE;
                    int k = i - Integer.MIN_VALUE;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"/tt/TestJava.java:7: JML result of numeric operation is out of range of the target type"
                ,"END -1"
                );
    }

    @Test public void testDiffJavaLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = Long.MAX_VALUE;
                    long k = i - Long.MIN_VALUE;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END -1"
                );
    }

    @Test public void testDiffSafeLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = Long.MAX_VALUE;
                    long k = i - Long.MIN_VALUE;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"/tt/TestJava.java:7: JML result of numeric operation is out of range of the target type"
                ,"END -1"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testDiffMath() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MAX_VALUE;
                    long k = i - Integer.MIN_VALUE;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 4294967295"
                );
    }

    @Test public void testDivJava() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MIN_VALUE;
                    int k = i / (-1);
                    System.out.println("END " + (k==i));
                  }
                }
                """
                ,"END true"
                );
    }

    @Test public void testDivSafe() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MIN_VALUE;
                    int k = i / (-1);
                    System.out.println("END " + (k==i));
                  }
                }
                """
                ,"/tt/TestJava.java:7: JML result of numeric operation is out of range of the target type"
                ,"END true"
                );
    }

    @Test public void testDivJavaLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = Long.MIN_VALUE;
                    long k = i / (-1);
                    System.out.println("END " + (k==i));
                  }
                }
                """
                ,"END true"
                );
    }

    @Test public void testDivSafeLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = Long.MIN_VALUE;
                    long k = i / (-1);
                    System.out.println("END " + (k==i));
                  }
                }
                """
                ,"/tt/TestJava.java:7: JML result of numeric operation is out of range of the target type"
                ,"END true"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testDivMath() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = Integer.MIN_VALUE;
                    long k = i / (-1);
                    System.out.println("END " + (-k==i));
                  }
                }
                """
                ,"END true"
                );
    }

    @Test public void testMultJava() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = 30000;
                    int k = i * i;
                    System.out.println("END " + k);
                    i = 70000;
                    k = i * i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 900000000"
                ,"END 605032704"
                );
    }

    @Test public void testMultSafe() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = 30000;
                    int k = i * i;
                    System.out.println("END " + k);
                    i = 70000;
                    k = i * i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 900000000"
                ,"/tt/TestJava.java:10: JML result of numeric operation is out of range of the target type"
                ,"END 605032704"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testMultMath() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    int i = 30000;
                    int k = i * i;
                    System.out.println("END " + k);
                    i = 70000;
                    k = i * i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 900000000"
                ,"/tt/TestJava.java:10: JML argument to numeric cast is out of range of the target type"
                ,"END 605032704"
                );
    }

    @Test public void testMultJavaLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = 2000000000L;
                    long k = i * i;
                    System.out.println("END " + k);
                    i = 5000000000L;
                    k = i * i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 4000000000000000000"
                ,"END 6553255926290448384"
                );
    }

    @Test public void testMultSafeLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = 2000000000L;
                    long k = i * i;
                    System.out.println("END " + k);
                    i = 5000000000L;
                    k = i * i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 4000000000000000000"
                ,"/tt/TestJava.java:10: JML result of numeric operation is out of range of the target type"
                ,"END 6553255926290448384"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testMultMathLong() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath
                public class TestJava {
                  public static void main(String[] args) {
                    long i = 2000000000L;
                    long k = i * i;
                    System.out.println("END " + k);
                    i = 5000000000L;
                    k = i * i;
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 4000000000000000000"
                ,"/tt/TestJava.java:10: JML argument to numeric cast is out of range of the target type"
                ,"END 6553255926290448384"
                );
    }

    @Test
    public void testModJava() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeJavaMath @SpecSafeMath
                public class TestJava {
                  public static void main(String... args) {
                    int k = 7 ;
                    int j = 3;
                    int m = 1;
                    int qq = 2;
                    int i = k % j;
                    int q = k / j;
                    //@ assert i == m && q == qq ;
                    //@ assert (k%j) == m && (k/j) == qq;
                    i = (-k) % j;
                    q = (-k) / j;
                    //@ assert i == -m && q == -qq;
                    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq; // Line 17
                    i = k % -j;
                    q = k / -j;
                    //@ assert i == m && q == -qq;
                    //@ assert (k%-j) == m && (k/-j) == -qq;
                    i = -k % -j; // Line 22
                    q = -k / -j;
                    //@ assert i == -m && q == qq;
                    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;
                  }
                }
                """
              );
    }

    @Test
    public void testModSafe() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeSafeMath @SpecSafeMath
                public class TestJava {
                  public static void main(String... args) {
                    int k = 7 ;
                    int j = 3;
                    int m = 1;
                    int qq = 2;
                    int i = k % j;
                    int q = k / j;
                    //@ assert i == m && q == qq ;
                    //@ assert (k%j) == m && (k/j) == qq;
                    i = (-k) % j;
                    q = (-k) / j;
                    //@ assert i == -m && q == -qq;
                    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq; // Line 17
                    i = k % -j;
                    q = k / -j;
                    //@ assert i == m && q == -qq;
                    //@ assert (k%-j) == m && (k/-j) == -qq;
                    i = -k % -j; // Line 22
                    q = -k / -j;
                    //@ assert i == -m && q == qq;
                    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;
                  }
                }
                """
              );
    }

    @Ignore // No CodeBigintMath as yet
    @Test
    public void testModMath() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                @CodeBigintMath @SpecBigintMath
                public class TestJava {
                  public static void main(String... args) {
                    int k = 7 ;
                    int j = 3;
                    int m = 1;
                    int qq = 2;
                    int i = k % j;
                    int q = k / j;
                    //@ assert i == m && q == qq ;
                    //@ assert (k%j) == m && (k/j) == qq;
                    i = (-k) % j;
                    q = (-k) / j;
                    //@ assert i == -m && q == -qq;
                    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq; // Line 17
                    i = k % -j;
                    q = k / -j;
                    //@ assert i == m && q == -qq;
                    //@ assert (k%-j) == m && (k/-j) == -qq;
                    i = -k % -j; // Line 22
                    q = -k / -j;
                    //@ assert i == -m && q == qq;
                    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;
                  }
                }
                """
              );
    }

}
