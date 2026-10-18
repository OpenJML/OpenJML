package org.jmlspecs.openjmltest.testsuites;

import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** The escfp tests with float and double modeled as reals that track NaN, infinities and signed zeros
 * (--fpreal). Results that depend only on those special values are the same as with the FloatingPoint theory;
 * the tests overridden here differ because the real model has no rounding, overflow or underflow. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfpreal extends escfp {

    @Override
    protected String fpOption() {
        return "--fpreal";
    }

    @Test
    public void testVacuityMulDivFails() {
        // as escfp.testVacuityFails, for the operations that are slow with the FloatingPoint theory
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(double a, double b) {
                    double c = a * b, d = a / b, e = a % b;
                    //@ assert false;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    @Test @Override
    public void testAddDouble() {
        // differs from escfp (exact sums): 0.1 + 0.2 is not rounded to 0.30000000000000004
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
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    @Test @Override
    public void testAddFloat() {
        // differs from escfp (exact sums): 0.1f + 0.2f is not rounded to 0.3f
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
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    @Test @Override
    public void testAbsorption() {
        // differs from escfp (no rounding): 1e16 + 1.0 differs from 1e16
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
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    @Test @Override
    public void testMixedTypes() {
        // differs from escfp (int to float is exact): 16777217 is not rounded
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
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    @Test @Override
    public void testFloatDoubleConversion() {
        // differs from escfp (double to float is exact): (float)0.1 is not rounded to 0.1f
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
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    @Test @Override
    public void testNotAssociativeFixed() {
        // differs from escfp: exact sums are associative
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
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    @Test @Override
    public void testOverflow() {
        // differs from escfp (no overflow): MAX_VALUE + MAX_VALUE is finite
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
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    @Test @Override
    public void testStrictMonotonicityFails() {
        // differs from escfp: exact sums are strictly monotonic
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
                );
    }

    @Test @Override
    public void testSuccessorFails() {
        // differs from escfp (no rounding): adding a positive value increases a finite value
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
                );
    }

    @Test @Override
    public void testBitPatterns() {
        // differs from escfp: bit patterns follow only from the specs; literal patterns, the inverse direction and
        // the sign bit are not provable with reals
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void roundTrip(float f, double d) {
                    //@ assert Float.identical(Float.intBitsToFloat(Float.floatToRawIntBits(f)), f);
                    //@ assert Double.identical(Double.longBitsToDouble(Double.doubleToLongBits(d)), d);
                  }
                  public void injective(float f, float g, double d, double e) {
                    //@ assert (Float.floatToIntBits(f) == Float.floatToIntBits(g)) == Float.identical(f, g);
                    //@ assert (Double.doubleToLongBits(d) == Double.doubleToLongBits(e)) == Double.identical(d, e);
                  }
                  public void special(float f) {
                    //@ assert Float.floatToRawIntBits(Float.POSITIVE_INFINITY) == 0x7f800000 && Float.floatToRawIntBits(-0.0f) == 0x80000000;
                    //@ assert Float.isNaN(f) ==> Float.floatToIntBits(f) == 0x7fc00000;
                  }
                  public void javaCode(float f) {
                    int i = Float.floatToIntBits(f);
                    float g = Float.intBitsToFloat(i);
                    //@ assert Float.identical(f, g);
                  }
                }
                """
                );
    }
}
