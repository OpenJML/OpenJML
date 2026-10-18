package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** ESC of float and double multiplication, division and remainder with the SMT FloatingPoint theory
 * (--no-fpreal). These are slow (the solver bit-blasts the operations; a symbolic double remainder can take
 * many minutes), so the tests run only when the system property RUNSLOWFP is set (e.g. OPENJML_JVM=-DRUNSLOWFP).
 * The fast floating-point tests are in escfp. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfpslow extends EscBase {

    static boolean runSlowFP = System.getProperty("RUNSLOWFP") != null;

    @Override
    public void setUp() throws Exception {
        Assume.assumeTrue(runSlowFP);
        super.setUp();
        addOptions("--no-fpreal");
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
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Postcondition) in method m",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
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
        // Java's % truncates the quotient, unlike the IEEE remainder (Math.IEEEremainder(7.0, 2.0) is -1.0)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a == 5.5 && b == 2.0 && c == 7.0;
                  public void m(double a, double b, double c) {
                    //@ assert a % b == 1.5;
                    //@ assert -a % b == -1.5;
                    //@ assert a % -b == 1.5;
                    //@ assert c % b == 1.0;
                    //@ assert Double.isNaN(a % 0.0);
                    //@ assert a % Double.POSITIVE_INFINITY == a;
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
}
