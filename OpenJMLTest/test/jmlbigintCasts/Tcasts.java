// ESC: a cast of a \bigint to an integral type narrows as Java does -- the value modulo 2^n, in the type's
// range (char is unsigned) -- in every arithmetic mode; the modes differ only in whether an out-of-range
// argument is warned about (#1018):
//   m0-m4: Java math (the test's --spec-math=java): no warning
//   s0-s4: Safe math: an ArithmeticCastRange warning for each cast
//   b0-b4: \bigint math: an ArithmeticCastRange warning for each cast
// (Long.MIN_VALUE + 49L, not + 49: see #1019.)
// Each checking method requires z == 50, so each argument is just above the type's maximum and each
// check tests the narrowed value.
// m5-m9 call the explicit conversion methods (byteValue() etc.), whose precondition requires an in-range value.
// Also: casts between Java integral types (including char) and the bit-vector encoding, in test/gitbug1018;
// RAC, in test/jmlbigint (Tcasts.java).
public class Tcasts {
    //@ ghost public static \bigint z = \bigint.one*50;
  //@ requires z == 50;
  public static void main(String... args) {
      m1(); m2(); m3(); m4(); m5(); m6(); m7(); m8(); m9();
  }
  
  //@ requires z == 50;
  public static /*@ pure */ void m0() {
      /*@ show (byte)(z+Byte.MAX_VALUE); */
      //@ check (byte)(z+Byte.MAX_VALUE) == -79;
  }
  //@ requires z == 50;
  public static /*@ pure */ void m1() {
      /*@ show (short)(z+Short.MAX_VALUE); */
      //@ check (short)(z+Short.MAX_VALUE) == -32719;
  }
  //@ requires z == 50;
  public static /*@ pure */ void m2() {
      /*@ show (char)(z+2*Character.MAX_VALUE); */
      //@ check (char)(z+2*Character.MAX_VALUE) == 48;
  }
  //@ requires z == 50;
  public static /*@ pure */ void m3() {
      /*@ show (int)(z+Integer.MAX_VALUE); */
      //@ check (int)(z+Integer.MAX_VALUE) == -2147483599;
  }
  //@ requires z == 50;
  public static /*@ pure */ void m4() {
      /*@ show (long)(z+Long.MAX_VALUE); */
      //@ check (long)(z+Long.MAX_VALUE) == Long.MIN_VALUE + 49L;
  }
  public static void m5() {
      /*@ show (z+Byte.MAX_VALUE).byteValue(); */
  }
  public static void m6() {
      /*@ show (z+Short.MAX_VALUE).shortValue(); */
  }
  public static void m7() {
      /*@ show (z+2*Character.MAX_VALUE).charValue(); */
  }
  public static void m8() {
      /*@ show (z+Integer.MAX_VALUE).intValue(); */
  }
  public static void m9() {
      /*@ show (z+Long.MAX_VALUE).longValue(); */
  }

  //@ requires z == 50;
  //@ code_safe_math spec_safe_math
  public static void s0() {
      //@ check (byte)(z+Byte.MAX_VALUE) == -79;
  }
  //@ requires z == 50;
  //@ code_safe_math spec_safe_math
  public static void s1() {
      //@ check (short)(z+Short.MAX_VALUE) == -32719;
  }
  //@ requires z == 50;
  //@ code_safe_math spec_safe_math
  public static void s2() {
      //@ check (char)(z+2*Character.MAX_VALUE) == 48;
  }
  //@ requires z == 50;
  //@ code_safe_math spec_safe_math
  public static void s3() {
      //@ check (int)(z+Integer.MAX_VALUE) == -2147483599;
  }
  //@ requires z == 50;
  //@ code_safe_math spec_safe_math
  public static void s4() {
      //@ check (long)(z+Long.MAX_VALUE) == Long.MIN_VALUE + 49L;
  }
  //@ requires z == 50;
  //@ code_bigint_math spec_bigint_math
  public static void b0() {
      //@ check (byte)(z+Byte.MAX_VALUE) == -79;
  }
  //@ requires z == 50;
  //@ code_bigint_math spec_bigint_math
  public static void b1() {
      //@ check (short)(z+Short.MAX_VALUE) == -32719;
  }
  //@ requires z == 50;
  //@ code_bigint_math spec_bigint_math
  public static void b2() {
      //@ check (char)(z+2*Character.MAX_VALUE) == 48;
  }
  //@ requires z == 50;
  //@ code_bigint_math spec_bigint_math
  public static void b3() {
      //@ check (int)(z+Integer.MAX_VALUE) == -2147483599;
  }
  //@ requires z == 50;
  //@ code_bigint_math spec_bigint_math
  public static void b4() {
      //@ check (long)(z+Long.MAX_VALUE) == Long.MIN_VALUE + 49L;
  }
}
