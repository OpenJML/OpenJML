package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** ESC of float and double multiplication, division and remainder with the SMT FloatingPoint theory
 * (--no-fpreal). These are slow (the solver bit-blasts the operations; a symbolic double remainder can take
 * many minutes), so the tests run only when the environment variable RUNSLOWFP is set (e.g. RUNSLOWFP=1 ./runtests
 * escfpslow).
 * The fast floating-point tests are in escfp. Some valid properties are left out because z3 cannot prove them in its
 * time limit, e.g. a <= b && Double.isFinite(c) ==> a + c <= b + c. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfpslow extends EscBase {

    static boolean runSlowFP = System.getenv("RUNSLOWFP") != null;

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--no-fpreal");
    }

    /** Checks the source only when RUNSLOWFP is set (OpenJMLTestRunner counts a JUnit assumption failure as a failure) */
    @Override
    protected void helpEsc(String classname, String inputSource, Object... expectedResults) {
        if (runSlowFP) super.helpEsc(classname, inputSource, expectedResults);
    }

    @Test
    public void testMulCommutativity() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures Float.identical(\\result, b * a);
                  public float m(float a, float b) {
                    return a * b;
                  }
                }
                """
                );
    }

    @Test
    public void testAdditionSigns() {
        // (from escfpPrimitiveOps)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(a+b);
                  public void m(double a, double b) {
                    double c = a + b;
                    //@ assert (a > 0.0) && (b > 0.0) ==> (c > 0.0);
                    //@ assert (a < 0.0) && (b < 0.0) ==> (c < 0.0);
                    //@ assert (a > 0.0) && (b < 0.0) && (Math.abs(a) > Math.abs(b)) ==> (c > 0.0);
                    //@ assert (a > 0.0) && (b < 0.0) && (Math.abs(a) < Math.abs(b)) ==> (c < 0.0);
                  }
                }
                """
                );
    }

    @Test
    public void testMulLaws() {
        // laws of * that hold for finite values (from escfpPrimitiveOps)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isFinite(a) && Double.isFinite(b);
                  public void m(double a, double b) {
                    //@ assert a * 1 == a && a * 1.0f == a;
                    //@ assert a * b == b * a;
                  }
                }
                """
                );
    }

    @Test
    public void testMulLawsFail() {
        // laws of * that do not hold, even for finite values (from escfpPrimitiveOps); the solver cannot settle
        // others within its time limit (distributivity, polynomial expansions, linear systems, ordering)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c);
                  public void assoc(float a, float b, float c) {
                    //@ assert (a * b) * c == a * (b * c);
                  }
                  //@ requires Float.isFinite(a);
                  public void inverse(float a) {
                    //@ assert a != 0 ==> a * (1 / a) == 1;
                  }
                  //@ requires Float.isFinite(a) && Float.isFinite(b);
                  public void sign(float a, float b) {
                    //@ assert (a > 0 && b > 0) ==> (a * b > 0); // underflow
                  }
                  //@ requires Float.isFinite(a);
                  public void comm(float a, float b) {
                    //@ assert a * b == b * a; // b may be NaN
                  }
                  //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d);
                  public void linear(float a, float b, float c, float d) {
                    //@ assert (a == b * c + d && b != 0 ) ==>  c == (a - d) / b;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method assoc",9
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method inverse",9
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method sign",9
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assert) in method comm",9
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assert) in method linear",9
                );
    }

    @Test
    public void testMulMonotonicityFails() {
        // fails by overflow: 2*a and 2*b may both be infinite
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a < b;
                  //@ ensures 2*a < 2*b;
                  public void m(double a, double b) {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Postcondition: /tt/TestJava.java:4:) in method m",15
                ,"/tt/TestJava.java:4: verify: Associated declaration: /tt/TestJava.java:5:",7
                );
    }

    @Test
    public void testMulMonotonicity() {
        // holds: rounding is monotonic, and a <= b excludes NaN
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a <= b;
                  //@ ensures 2*a <= 2*b;
                  public void m(double a, double b) {
                  }
                }
                """
                );
    }

    @Test
    public void testMulNonNegative() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires r >= 0;
                  //@ ensures \\result >= 0;
                  public double m(double r) {
                    return 3.14 * r * r;
                  }
                }
                """
                );
    }

    @Test
    public void testDivision() {
        // division by zero is defined (no DivideByZero warning)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isPositiveZero(z) && one == 1.0;
                  public void m(double z, double one) {
                    //@ assert one / z == Double.POSITIVE_INFINITY;
                    //@ assert one / -z == Double.NEGATIVE_INFINITY;
                    //@ assert Double.isNaN(z / z);
                    //@ assert Double.isNegativeZero(-one / Double.POSITIVE_INFINITY);
                    double q = one / 3.0;
                    //@ assert q * 3.0 == one;
                  }
                }
                """
                );
    }

    @Test
    public void testDivisionZeroSignFails() {
        // z == 0.0 holds for -0.0 too
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires z == 0.0;
                  public void m(double z) {
                    //@ assert 1.0 / z == Double.POSITIVE_INFINITY;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    @Test
    public void testRemainder() {
        // Java's % truncates the quotient, unlike the IEEE remainder (Math.IEEEremainder(7.0, 2.0) is -1.0); float, since
        // double % times out even on these values
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a == 5.5f && b == 2.0f && c == 7.0f;
                  public void m(float a, float b, float c) {
                    //@ assert a % b == 1.5f;
                    //@ assert -a % b == -1.5f;
                    //@ assert a % -b == 1.5f;
                    //@ assert c % b == 1.0f;
                    //@ assert Float.isNaN(a % 0.0f);
                    //@ assert a % Float.POSITIVE_INFINITY == a;
                  }
                }
                """
                );
    }

    @Test
    public void testRemainderFloat() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires b > 0 && Float.isFinite(a);
                  //@ ensures Float.isNaN(\\result) || (-b < \\result && \\result < b);
                  public float m(float a, float b) {
                    return a % b;
                  }
                }
                """
                );
    }

    @Test
    public void testNaNMulDiv() {
        // (from escfpPrimitiveOps)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(double a, double b) {
                    //@ assert (Double.isNaN(a) || Double.isNaN(b)) ==> Double.isNaN(a * b);
                    //@ assert (Double.isInfinite(a) && (b == 0.0)) ==> Double.isNaN(a * b);
                    //@ assert (Double.isNaN(a) || Double.isNaN(b)) ==> Double.isNaN(a / b);
                    //@ assert (Double.isInfinite(a) && Double.isInfinite(b)) ==> Double.isNaN(a / b);
                    //@ assert ((a == 0.0) && (b == 0.0)) ==> Double.isNaN(a / b);
                  }
                }
                """
                );
    }

    @Test
    public void testInfinityMulDiv() {
        // (from escfpPrimitiveOps)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires !Double.isNaN(a) && !Double.isNaN(b);
                  public void m(double a, double b) {
                    //@ assert (a == Double.POSITIVE_INFINITY && b == 0.0) ==> Double.isNaN(a * b);
                    //@ assert (a == Double.POSITIVE_INFINITY && b > 0.0) ==> (a * b) == Double.POSITIVE_INFINITY;
                    //@ assert (a == Double.NEGATIVE_INFINITY && b < 0.0) ==> (a * b) == Double.POSITIVE_INFINITY;
                    //@ assert (Double.isInfinite(a) && Double.isInfinite(b)) ==> Double.isNaN(a / b);
                    //@ assert (a == Double.POSITIVE_INFINITY && (b > 0.0 && b < Double.POSITIVE_INFINITY)) ==> (a / b) == Double.POSITIVE_INFINITY;
                    //@ assert (Double.isFinite(a) && Double.isInfinite(b)) ==> (a / b) == 0.0;
                    //@ assert (a != 0.0 && b == 0.0) ==> Double.isInfinite(a / b);
                  }
                }
                """
                );
    }

    @Test
    public void testUnderflowFails() {
        // a nonzero product can underflow to zero (gitbug735; with --fpreal m2 verifies: escfp.testRealSemantics)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires -1000 < a < 1000;
                  public void m(double a) {
                    //@ assert (a == 0) | (a*a != 0);
                  }
                  public void m2(double a, double b, double c, double d) {
                    //@ assert ((a - b) * (c - d) == 0) ==> (a == b || c == d);
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m",9
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method m2",9
                );
    }

    @Test
    public void testMathFunctions() {
        // Math methods that are IEEE operations are translated exactly (incl. gitbug732)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires x == 2.25 && y == -3.5;
                  public void copySign(double x, double y) {
                    //@ assert Math.copySign(64.0, y) == -64.0 && Math.copySign(-64.0, x) == 64.0;
                  }
                  //@ requires x == 2.25 && y == -3.5;
                  public void sqrt(double x, double y) {
                    //@ assert Math.sqrt(x) == 1.5 && Double.isNaN(Math.sqrt(y));
                  }
                  //@ requires y == -3.5;
                  public void rounding(double y) {
                    //@ assert Math.floor(y) == -4.0 && Math.ceil(y) == -3.0 && Math.rint(y) == -4.0;
                    //@ assert Double.isNegativeZero(Math.ceil(-0.5));
                  }
                  //@ requires x == 2.25 && y == -3.5;
                  public void minmax(double x, double y) {
                    //@ assert Math.min(x, y) == y && Math.max(x, y) == x && Math.abs(y) == 3.5;
                    //@ assert Double.isPositiveZero(Math.max(-0.0, 0.0)) && Double.isNegativeZero(Math.min(0.0, -0.0));
                    //@ assert Double.isNaN(Math.max(x, Double.NaN));
                  }
                }
                """
                );
    }

    @Test
    public void testMathIntArguments() {
        // int arguments are converted to float (gitbug732); z3 times out on int to float conversions
        addOptions("--prover=cvc5-1.3.2");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 64 && j == -128;
                  public void m(int i, int j) {
                    //@ assert (int)Math.copySign(i, j) == -64;
                  }
                }
                """
                );
    }

    @Test
    public void testIssue960() {
        // NaN and infinite arguments make the result NaN, so these postconditions do not hold
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures Math.abs(\\result - (x+y)) < 0.001;
                  public double sum(double x, double y) {
                    return x+y;
                  }
                  //@ requires Double.isFinite(x) && Double.isFinite(y) && Double.isFinite(x+y);
                  //@ ensures Math.abs(\\result - (x+y)) < 0.001;
                  public double sum2(double x, double y) {
                    return x+y;
                  }
                  //@ requires !Double.isNaN(x) && !Double.isNaN(y);
                  //@ ensures Math.abs(\\result - (x+y)/2.0) < 0.001;
                  public double average(double x, double y) {
                    return (x+y)/2.0;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Postcondition: /tt/TestJava.java:3:) in method sum",5
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:5:",7
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Postcondition: /tt/TestJava.java:13:) in method average",5
                ,"/tt/TestJava.java:13: verify: Associated declaration: /tt/TestJava.java:15:",7
                );
    }
}
