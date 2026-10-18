package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** ESC of float and double with the SMT FloatingPoint theory (--no-fpreal): arithmetic, properties that do
 * and do not hold, and IEEE behavior of NaN, infinities and signed zeros. Values come from parameters (fixed
 * by preconditions or assumptions), so that javac does not fold the expressions into constants.
 * Multiplication, division and remainder are slow to verify; they are tested in escfpslow. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfp extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--no-fpreal");
    }

    // Arithmetic computations

    @Test
    public void testAddDouble() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a == 0.1 && b == 0.2;
                  public void m(double a, double b) {
                    double c = a + b;
                    //@ assert c != 0.3;
                    //@ assert c == 0.30000000000000004;
                    //@ assert c - b != a;
                  }
                }
                """
                );
    }

    @Test
    public void testAddFloat() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a == 0.1f && b == 0.2f;
                  public void m(float a, float b) {
                    float c = a + b;
                    //@ assert c == 0.3f;
                    double d = (double)a + (double)b;
                    //@ assert d != 0.3;
                  }
                }
                """
                );
    }

    @Test
    public void testAbsorption() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a == 1e16 && f == 16777216.0f;
                  public void m(double a, float f) {
                    //@ assert a + 1.0 == a;
                    //@ assert f + 1.0f == f;
                    //@ assert (double)f + 1.0 != f;
                  }
                }
                """
                );
    }

    @Test
    public void testMixedTypes() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 16777217 && f == 0.5f;
                  public void m(int i, float f) {
                    float g = i;          // rounds
                    //@ assert g == 16777216.0f;
                    double d = i;         // exact
                    //@ assert d == 16777217.0;
                    double e = f + 0.25;  // float promoted to double
                    //@ assert e == 0.75;
                  }
                }
                """
                );
    }

    // Properties that hold

    @Test
    public void testCommutativity() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures Double.identical(\\result, b + a);
                  public double m(double a, double b) {
                    return a + b;
                  }
                  //@ ensures Float.identical(\\result, b + a);
                  public float mf(float a, float b) {
                    return a + b;
                  }
                }
                """
                );
    }

    @Test
    public void testIdentities() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(double a, double b) {
                    //@ assert Double.identical(-(-a), a);
                    //@ assert Double.identical(a - b, a + (-b));
                    //@ assert Double.identical(a + -0.0, a);
                    //@ assert Double.isNaN(a) || a + 0.0 == a;
                  }
                }
                """
                );
    }

    @Test
    public void testMonotonicity() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a <= b && Double.isFinite(c);
                  //@ ensures a + c <= b + c;
                  public void m(double a, double b, double c) {
                  }
                  //@ requires a <= b;
                  //@ ensures a + a <= b + b;
                  public void m2(double a, double b) {
                  }
                }
                """
                );
    }

    @Test
    public void testMonotonicityFails() {
        // fails for infinite c: a == -c and b == c make a + c NaN
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a <= b && !Double.isNaN(c);
                  //@ ensures a + c <= b + c;
                  public void m(double a, double b, double c) {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Postcondition) in method m",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    // Properties that do not always hold

    @Test
    public void testNotAssociative() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures (a + b) + c == a + (b + c);
                  public void m(double a, double b, double c) {
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Postcondition) in method m",15
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    @Test
    public void testNotAssociativeFixed() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a == 0.1 && b == 0.2 && c == 0.3;
                  public void m(double a, double b, double c) {
                    //@ assert (a + b) + c != a + (b + c);
                  }
                }
                """
                );
    }

    @Test
    public void testStrictMonotonicityFails() {
        // fails by overflow: a + a and b + b may both be infinite
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a < b;
                  //@ ensures a + a < b + b;
                  public void m(double a, double b) {
                  }
                  //@ requires a < b && Double.isFinite(c);
                  //@ ensures a + c < b + c;
                  public void m2(double a, double b, double c) {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Postcondition) in method m",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method m2",15
                ,"/tt/TestJava.java:8: verify: Associated declaration",7
                );
    }

    @Test
    public void testSuccessorFails() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isFinite(a);
                  //@ ensures a + 1 > a;
                  public void m(double a) {
                  }
                  //@ requires -1e10 < a < 1e10;
                  //@ ensures a + 1 > a;
                  public void m2(double a) {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Postcondition) in method m",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    @Test
    public void testReflexivityFails() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(double a) {
                    //@ assert a == a;
                  }
                  public void m2(double a) {
                    //@ assert a - a == 0;
                  }
                  public void m3(double a) {
                    //@ assert Double.identical(a + 0.0, a);
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m",9
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m2",9
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m3",9
                );
    }

    @Test
    public void testOverflow() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a == Double.MAX_VALUE;
                  public void m(double a) {
                    double b = a + a;
                    //@ assert Double.isInfinite(b) && b > a;
                    //@ assert b == Double.POSITIVE_INFINITY;
                    //@ assert -a - a == Double.NEGATIVE_INFINITY;
                  }
                }
                """
                );
    }

    // IEEE behavior of NaN, infinities and signed zeros

    @Test
    public void testNaN() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isNaN(n) && !Double.isNaN(x);
                  public void m(double n, double x) {
                    //@ assert n != n;
                    //@ assert !(n == n);
                    //@ assert n != x && !(n == x);
                    //@ assert !(n < x) && !(n <= x) && !(n > x) && !(n >= x);
                    //@ assert Double.isNaN(n + x) && Double.isNaN(x - n);
                    //@ assert Double.identical(n, Double.NaN);
                    //@ assert !Double.isFinite(n) && !Double.isInfinite(n);
                  }
                  //@ requires Float.isNaN(n);
                  public void mf(float n) {
                    //@ assert n != n;
                    //@ assert Float.identical(n, Float.NaN);
                  }
                }
                """
                );
    }

    @Test
    public void testNaNConstant() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(double x) {
                    double n = Double.NaN;
                    //@ assert Double.isNaN(n);
                    //@ assert n != n;
                    //@ assert Double.isNaN(n + x);
                  }
                }
                """
                );
    }

    @Test
    public void testInfinity() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires p == Double.POSITIVE_INFINITY && Double.isFinite(x);
                  public void m(double p, double x) {
                    //@ assert Double.isInfinite(p) && !Double.isFinite(p);
                    //@ assert p > Double.MAX_VALUE && -p < -Double.MAX_VALUE;
                    //@ assert p + x == p && p - x == p && x - p == -p;
                    //@ assert p + p == p;
                    //@ assert Double.isNaN(p - p) && Double.isNaN(p + (-p));
                    //@ assert -p == Double.NEGATIVE_INFINITY;
                  }
                }
                """
                );
    }

    @Test
    public void testSignedZero() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isPositiveZero(z);
                  public void m(double z) {
                    double nz = -z;
                    //@ assert Double.isNegativeZero(nz);
                    //@ assert nz == z;
                    //@ assert !Double.identical(nz, z);
                    //@ assert Double.isPositiveZero(z + nz);
                    //@ assert Double.isNegativeZero(nz + nz);
                    //@ assert Double.isPositiveZero(z - z);
                  }
                }
                """
                );
    }

    @Test
    public void testSignedZeroFails() {
        // z == 0.0 holds for both zeros
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires z == 0.0;
                  public void m(double z) {
                    //@ assert Double.isPositiveZero(z);
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    // Conversions

    @Test
    public void testCasts() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isNaN(n) && p == Double.POSITIVE_INFINITY && x == -2.7 && y == 1e10;
                  public void m(double n, double p, double x, double y) {
                    //@ assert (int)n == 0 && (long)n == 0;
                    //@ assert (int)p == Integer.MAX_VALUE && (long)p == Long.MAX_VALUE;
                    //@ assert (int)-p == Integer.MIN_VALUE && (long)-p == Long.MIN_VALUE;
                    //@ assert (int)x == -2 && (long)x == -2;
                    //@ assert (int)y == Integer.MAX_VALUE && (long)y == 10000000000L;
                    //@ assert (short)y == -1 && (char)x == 65534;
                  }
                }
                """
                );
    }

    @Test
    public void testFloatDoubleConversion() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires f == 0.1f && d == 0.1;
                  public void m(float f, double d) {
                    double df = f;          // exact
                    //@ assert df != d;
                    //@ assert (float)df == f;
                    float fd = (float)d;    // rounds
                    //@ assert fd == f;
                    //@ assert (double)fd != d;
                  }
                }
                """
                );
    }

    @Test
    public void testLiteralCasts() {
        // also a regression test for casts of floating-point literals to integral types (formerly an SMT sort error)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    int i = (int) -2.7;
                    short s = (short) 1e10;
                    char c = (char) 65.9;
                    byte b = (byte) 300.5f;
                    long k = (long) 1e30;
                    //@ assert i == -2 && s == -1 && c == 'A' && b == 44 && k == Long.MAX_VALUE;
                  }
                }
                """
                );
    }

    @Test
    public void testLiteralCastsReal() {
        addOptions("--fpreal");
        testLiteralCasts();
    }

    @Test
    public void testRealConversion() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a == 0.5 && f == 0.25f;
                  public void m(double a, float f) {
                    //@ assert (\\real)a == 0.5;
                    //@ assert (\\real)a + (\\real)f == 0.75;
                  }
                }
                """
                );
    }

    @Test
    public void testBoxed() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a == 1.5;
                  public void m(double a) {
                    Double b = a;
                    double c = b;
                    //@ assert c == 1.5;
                  }
                }
                """
                );
    }

    // The option

    @Test
    public void testRealSemantics() {
        // with --fpreal, float and double are modeled as reals: associativity holds (unsoundly, for Java)
        addOptions("--fpreal");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c);
                  //@ ensures (a + b) + c == a + (b + c);
                  public void m(double a, double b, double c) {
                  }
                }
                """
                );
    }

    @Test
    public void testBadOption() {
        addOptions("--fpreal=maybe");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                }
                """
                ,"warning: Command-line argument error: Expected 'auto', 'true' or 'false' for --fpreal: maybe",-1
                );
    }
}
