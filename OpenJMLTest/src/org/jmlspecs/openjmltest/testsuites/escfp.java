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
        addOptions("--prover=cvc5-1.3.2"); // z3 times out on int to float conversions (int2bv and FloatingPoint)
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

    @Test
    public void testLiterals() {
        // literal translation, incl. scientific notation and digits beyond the precision (from escfpPrimitiveOps)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires f == 1.2345678e7f && g == 1.23456789e7f && d == 1.23456789e7 && e == 9.99999e-7;
                  public void m(float f, float g, double d, double e) {
                    //@ assert f == 12345678.0f && g == 12345678.9f && g != f;
                    //@ assert d == 12345678.9 && d != f;
                    //@ assert e == 0.000000999999;
                    //@ assert f < 1.2345679e7f && 3.0f < 3.000001f && -5194.333f > -5483.456f;
                  }
                  //@ requires x == 12345678912345678.9 && y == 234243E20;
                  public void m2(double x, double y) {
                    //@ assert x == 12345678912345678.0 && x != 12345678912345679.0;
                    //@ assert y == 2.34243e25 && y < Double.POSITIVE_INFINITY;
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
    public void testRelationLaws() {
        // ==, <=, < on finite values (from escfpPrimitiveOps)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c);
                  public void m(double a, double b, double c) {
                    //@ assert a == a && ((a == b) <==> (b == a)) && ((a == b && b == c) ==> a == c);
                    //@ assert ((a == b) <==> !(a != b)) && ((a != b) ==> (a > b || a < b));
                    //@ assert a <= a && ((a <= b && b <= c) ==> a <= c) && ((a <= b) || (b <= a));
                    //@ assert ((a <= b) <==> (b >= a)) && ((a <= b) <==> !(a > b));
                    //@ assert !(a < a) && ((a < b) ==> !(b < a)) && ((a < b && b < c) ==> a < c);
                    //@ assert ((a <= b && b <= a) ==> a == b) && ((a <= b && b < c) ==> a < c);
                  }
                  //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c);
                  public void mf(float a, float b, float c) {
                    //@ assert a == a && ((a == b && b == c) ==> a == c) && ((a <= b) || (b <= a));
                    //@ assert ((a <= b) <==> !(a > b)) && ((a < b && b < c) ==> a < c);
                  }
                }
                """
                );
    }

    @Test
    public void testRelationLawsNaNFails() {
        // without finiteness, NaN is unordered
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(double a, double b) {
                    //@ assert (a <= b) || (b <= a);
                  }
                  public void m2(double a, double b) {
                    //@ assert (a <= b) <==> !(a > b);
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m",9
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m2",9
                );
    }

    @Test
    public void testAdditionLaws() {
        // laws of + that do hold for finite values (from escfpPrimitiveOps); associativity does not (testNotAssociative);
        // monotonicity is in escfpslow
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c) && Double.isFinite(d);
                  public void m(double a, double b, double c, double d) {
                    //@ assert a + 0 == a && a + 0.0f == a;
                    //@ assert a - a == 0 && a + -a == 0;
                    //@ assert a + b == b + a;
                    //@ assert (a == b ==> a + c == b + c) && (a == b ==> a - c == b - c);
                    //@ assert ((a > 0 && b > 0) ==> a + b > 0) && ((a <= 0 && b <= 0) ==> a + b <= 0);
                  }
                  //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d);
                  public void mf(float a, float b, float c, float d) {
                    //@ assert a + 0 == a && a - a == 0 && a + b == b + a;
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
    public void testNaNComparisons() {
        // comparisons with Double.NaN and finiteness of the constants (from escfpPrimitiveOps)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(double a) {
                    //@ assert a != Double.NaN && Double.NaN != a;
                    //@ assert !(a < Double.NaN) && !(a >= Double.NaN) && !(Double.NaN <= a);
                    //@ assert !Double.isNaN(0.0) && !Double.isNaN(-32049234.23423);
                    //@ assert !Double.isNaN(Double.MAX_VALUE) && !Double.isNaN(-Double.MIN_VALUE);
                    //@ assert Double.isFinite(Double.MAX_VALUE) && Double.MIN_VALUE > 0;
                  }
                }
                """
                );
    }

    @Test
    public void testInfinityComparisons() {
        // (from escfpPrimitiveOps)
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires p == Double.POSITIVE_INFINITY && n == Double.NEGATIVE_INFINITY && !Double.isNaN(a);
                  public void m(double p, double n, double a) {
                    //@ assert p != n && p > n && p == -n && n == -p;
                    //@ assert 0.0 < p && 0 > n && -23489348.23482934829348 > n;
                    //@ assert Double.MAX_VALUE < p && -Double.MAX_VALUE > n;
                    //@ assert n <= a && a <= p && (a != p ==> a < p) && (a != n ==> a > n);
                  }
                  //@ requires !Double.isNaN(a) && !Double.isNaN(b);
                  public void m2(double a, double b) {
                    //@ assert (a == Double.POSITIVE_INFINITY && b != Double.NEGATIVE_INFINITY) ==> (a + b) == Double.POSITIVE_INFINITY;
                    //@ assert (a != Double.POSITIVE_INFINITY && b == Double.NEGATIVE_INFINITY) ==> (a + b) == Double.NEGATIVE_INFINITY;
                    //@ assert (a == Double.POSITIVE_INFINITY && b == Double.NEGATIVE_INFINITY) ==> Double.isNaN(a + b);
                    //@ assert (a == Double.POSITIVE_INFINITY && b != Double.POSITIVE_INFINITY) ==> (a - b) == Double.POSITIVE_INFINITY;
                    //@ assert (a == Double.POSITIVE_INFINITY && b == Double.POSITIVE_INFINITY) ==> Double.isNaN(a - b);
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

    @Test
    public void testWrapperPitfallsFails() {
        // plausible but wrong claims from the old escDouble/escFloat tests: ==, compare and equals differ on
        // -0.0/+0.0, max propagates NaN, and !isFinite includes the infinities
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void equalsZero(double a, double b) {
                    Double x = a, y = b;
                    //@ assert (a == b) ==> x.equals(y);
                  }
                  public void compareZero(float a, float b) {
                    //@ assert (a == b) ==> Float.compare(a, b) == 0;
                  }
                  public void maxNaN(double a, double b) {
                    //@ assert Double.isNaN(a) ==> Double.max(a, b) == b;
                  }
                  public void notFinite(float a) {
                    //@ assert !Float.isFinite(a) ==> Float.isNaN(a);
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method equalsZero",9
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method compareZero",9
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method maxNaN",9
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assert) in method notFinite",9
                );
    }

    @Test
    public void testDoubleFloatMethods() {
        // Double/Float compare, sum, min, max are translated exactly
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires Double.isNaN(n) && Double.isPositiveZero(z) && x == 1.5;
                  public void m(double n, double z, double x) {
                    //@ assert Double.compare(-z, z) < 0 && Double.compare(z, -z) > 0 && Double.compare(z, z) == 0;
                    //@ assert Double.compare(n, n) == 0 && Double.compare(n, Double.POSITIVE_INFINITY) > 0;
                    //@ assert Double.compare(x, n) < 0 && Double.compare(x, 2.0) < 0 && Double.compare(x, -x) > 0;
                    //@ assert Double.sum(x, x) == 3.0 && Double.isNaN(Double.sum(x, n));
                    //@ assert Double.max(x, -x) == x && Double.isNegativeZero(Double.min(z, -z));
                  }
                  //@ requires f == 1.5f;
                  public void mf(float f) {
                    //@ assert Float.compare(f, 2.0f) < 0 && Float.compare(-0.0f, 0.0f) < 0;
                    //@ assert Float.sum(f, f) == 3.0f && Float.min(f, -f) == -f;
                  }
                }
                """
                );
    }

    // Conversions

    @Test
    public void testStringConversions() {
        // Float/Double valueOf, toString and parse specs for the special values (from escFloat/escDouble StringTests);
        // decimal digits are not specified
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void valueOf(float f, double d) {
                    Float b = Float.valueOf(f);
                    Double c = Double.valueOf(d);
                    //@ assert Float.identical(b.floatValue(), f) && Double.identical(c.doubleValue(), d);
                  }
                  public void toStringF(float f) {
                    String s = Float.toString(f);
                    //@ assert Float.isNaN(f) <==> s.equals("NaN");
                    //@ assert (f == Float.POSITIVE_INFINITY) <==> s.equals("Infinity");
                    //@ assert Float.isNegativeZero(f) <==> s.equals("-0.0");
                    //@ assert Float.identical(Float.parseFloat(s), f);
                  }
                  public void toStringD(double d) {
                    String s = Double.toHexString(d);
                    //@ assert (d == Double.NEGATIVE_INFINITY) <==> s.equals("-Infinity");
                    //@ assert Double.isPositiveZero(d) <==> s.equals("0x0.0p0");
                    //@ assert (d < 0) ==> s.charAt(0) == '-';
                  }
                  public void parse() {
                    //@ assert Float.isNaN(Float.parseFloat("NaN"));
                    //@ assert Double.parseDouble("-Infinity") == Double.NEGATIVE_INFINITY;
                    Float b = Float.valueOf("+Infinity");
                    //@ assert b.floatValue() == Float.POSITIVE_INFINITY;
                  }
                }
                """
                );
    }

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
                  // gitbug735: no underflow with reals (with FloatingPoint it fails: escfpslow.testUnderflowFails)
                  public void m2(double a, double b, double c, double d) {
                    //@ assert ((a - b) * (c - d) == 0) ==> (a == b || c == d);
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
