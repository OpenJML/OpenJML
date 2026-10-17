// RAC and ESC (primrac.jmlbigint, primesc1.jmlbigint): a cast of a \bigint to an integral type narrows as Java
// does -- the value modulo 2^n, in the type's range (char is unsigned) -- in every arithmetic mode; the modes
// differ only in whether an out-of-range argument is reported (#1018):
//   s0-s4: Safe math (the default): one "argument to numeric cast is out of range" report per cast
//          (m0-m4 show the same values, as before)
//   j0-j4: Java math: no report
//   b0-b4: \bigint math: one report per cast
// (Long.MIN_VALUE + 49L, not + 49: see #1019.)
// With z == 50, each argument is just above the type's maximum, so each check tests the narrowed value.
// m5-m9 call the explicit conversion methods (byteValue() etc.), which check their argument's range.
// Also: ESC, in test/jmlbigintCasts; casts between Java integral types (including char), in test/gitbug1018.
public class Tcasts {
  public static void main(String... args) { //-ESC@ set System.out.println("CASTS");
      m1(); m2(); m3(); m4(); m5(); m6(); m7(); m8(); m9(); m10(); p1((short)0); p2((short)0); p3((short)0); p4((short)0);
      s0(); s1(); s2(); s3(); s4(); j0(); j1(); j2(); j3(); j4(); b0(); b1(); b2(); b3(); b4();
  }
  
  public static void m0() {
      //@ ghost \bigint z = \bigint.one*50;
      /*@ show (byte)(z+Byte.MAX_VALUE); */
  }
  public static void m1() {
      //@ ghost \bigint z = \bigint.one*50;
      /*@ show (short)(z+Short.MAX_VALUE); */
  }
  public static void m2() {
      //@ ghost \bigint z = \bigint.one*50;
      /*@ show (char)(z+2*Character.MAX_VALUE); */
  }
  public static void m3() {
      //@ ghost \bigint z = \bigint.one*50;
      /*@ show (int)(z+Integer.MAX_VALUE); */
  }
  public static void m4() {
      //@ ghost \bigint z = \bigint.one*50;
      /*@ show (long)(z+Long.MAX_VALUE); */
  }
  public static void m5() {
      //@ ghost \bigint z = \bigint.one*50;
      /*@ show (z+Byte.MAX_VALUE).byteValue(); */
  }
  public static void m6() {
      //@ ghost \bigint z = \bigint.one*50;
      /*@ show (z+Short.MAX_VALUE).shortValue(); */
  }
  public static void m7() {
      //@ ghost \bigint z = \bigint.one*50;
      /*@ show (z+2*Character.MAX_VALUE).charValue(); */
  }
  public static void m8() {
      //@ ghost \bigint z = \bigint.one*50;
      /*@ show (z+Integer.MAX_VALUE).intValue(); */
  }
  public static void m9() {
      //@ ghost \bigint z = \bigint.one*50;
      /*@ show (z+Long.MAX_VALUE).longValue(); */
  }
  public static void m10() {
      //@ ghost \bigint z1 = (Integer)8;
      /*@ assert z1 == 8; */
      //@ ghost \bigint z2 = Short.valueOf((short)8);
      //@ show z2;
      /*@ assert z2 == 8; */
      //@ ghost \bigint z3 = Byte.valueOf((byte)8);
      //@ show z3;
      /*@ assert z3 == 8; */
      //@ ghost \bigint z4 = Character.valueOf((char)8);
      /*@ assert z4 == 8; */
      //@ ghost \bigint z5 = Long.valueOf(8L);
      /*@ assert z5 == 8; */
  }
  
  // Just testing these combinations (to make sure that the relevant range assumptions are implicitly applied)
  // Should not be different for the other primitive types.
  public static void p1(short s) {
      //@ ghost var ss = \bigint.of(s).shortValue();
  }
  public static void p2(short s) {
      //@ ghost var ss = (short)\bigint.of(s);
  }
  public static void p3(short s) {
      //@ ghost var ss = ((\bigint)s).shortValue();
  }
  public static void p4(short s) {
      //@ ghost var ss = (short)(\bigint)s;
  }

  //@ code_java_math spec_java_math
  public static void j0() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (byte)(z+Byte.MAX_VALUE) == -79;
  }
  //@ code_java_math spec_java_math
  public static void j1() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (short)(z+Short.MAX_VALUE) == -32719;
  }
  //@ code_java_math spec_java_math
  public static void j2() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (char)(z+2*Character.MAX_VALUE) == 48;
  }
  //@ code_java_math spec_java_math
  public static void j3() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (int)(z+Integer.MAX_VALUE) == -2147483599;
  }
  //@ code_java_math spec_java_math
  public static void j4() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (long)(z+Long.MAX_VALUE) == Long.MIN_VALUE + 49L;
  }
  //@ code_bigint_math spec_bigint_math
  public static void b0() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (byte)(z+Byte.MAX_VALUE) == -79;
  }
  //@ code_bigint_math spec_bigint_math
  public static void b1() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (short)(z+Short.MAX_VALUE) == -32719;
  }
  //@ code_bigint_math spec_bigint_math
  public static void b2() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (char)(z+2*Character.MAX_VALUE) == 48;
  }
  //@ code_bigint_math spec_bigint_math
  public static void b3() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (int)(z+Integer.MAX_VALUE) == -2147483599;
  }
  //@ code_bigint_math spec_bigint_math
  public static void b4() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (long)(z+Long.MAX_VALUE) == Long.MIN_VALUE + 49L;
  }
  public static void s0() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (byte)(z+Byte.MAX_VALUE) == -79;
  }
  public static void s1() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (short)(z+Short.MAX_VALUE) == -32719;
  }
  public static void s2() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (char)(z+2*Character.MAX_VALUE) == 48;
  }
  public static void s3() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (int)(z+Integer.MAX_VALUE) == -2147483599;
  }
  public static void s4() {
      //@ ghost \bigint z = \bigint.one*50;
      //@ check (long)(z+Long.MAX_VALUE) == Long.MIN_VALUE + 49L;
  }
}
