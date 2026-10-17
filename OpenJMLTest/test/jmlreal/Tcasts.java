// RAC and ESC (primrac.jmlreal, primesc2.jmlreal): a cast of a \real to an integral type converts as Java converts a
// double (#1018): rounded toward zero, then clamped to the range of int (or long), then, for short, char and byte,
// narrowed from int (wrapped). The modes differ only in whether an out-of-range argument is reported:
//   s0-s4: Safe math (the default): reported (m0-m4 show the same values, as before)
//   j0-j4: Java math: not reported
//   b0-b4: \bigint math: reported
// With z == 50, each argument is just above the type's maximum. For int and long the result is clamped (unlike a
// \bigint, which wraps: see test/jmlbigint); for short, char and byte it fits in an int and is then wrapped.
// f0: rounding toward zero. w0: (int)(\bigint)r rounds to a \bigint and then wraps, unlike (int)r, which clamps.
// m5-m9 call the explicit conversion methods (byteValue() etc.).
public class Tcasts {
  public static void main(String... args) { //-ESC@ set System.out.println("CASTS");
      m1(); m2(); m3(); m4(); m5(); m6(); m7(); m8(); m9(); m10(); m11(); p1((short)0); p2((short)0); p3((short)0); p4((short)0);
      s0(); s1(); s2(); s3(); s4(); j0(); j1(); j2(); j3(); j4(); b0(); b1(); b2(); b3(); b4(); f0(); w0();
  }
  
  public static void m0() {
      //@ ghost \real z = (\real)50;
      /*@ show (byte)(z+Byte.MAX_VALUE); */
  }
  public static void m1() {
      //@ ghost \real z = (\real)50;
      /*@ show (short)(z+Short.MAX_VALUE); */
  }
  public static void m2() {
      //@ ghost \real z = (\real)50;
      /*@ show (char)(z+2*Character.MAX_VALUE); */
  }
  public static void m3() {
      //@ ghost \real z = (\real)50;
      /*@ show (int)(z+Integer.MAX_VALUE); */
  }
  public static void m4() {
      //@ ghost \real z = (\real)50;
      /*@ show (long)(z+Long.MAX_VALUE); */
  }
  public static void m5() {
      //@ ghost \real z = (\real)50;
      /*@ show (z+Byte.MAX_VALUE).byteValue(); */
  }
  public static void m6() {
      //@ ghost \real z = (\real)50;
      /*@ show (z+Short.MAX_VALUE).shortValue(); */
  }
  public static void m7() {
      //@ ghost \real z = (\real)50;
      /*@ show (z+2*Character.MAX_VALUE).charValue(); */
  }
  public static void m8() {
      //@ ghost \real z = (\real)50;
      /*@ show (z+Integer.MAX_VALUE).intValue(); */
  }
  public static void m9() {
      //@ ghost \real z = (\real)50;
      /*@ show (z+Long.MAX_VALUE).longValue(); */
  }
  public static void m10() {
      //@ ghost \real z = (\real)Double.POSITIVE_INFINITY;
      //@ ghost \real y = (\real)Double.NaN;
  }
  public static void m11() {
      //@ ghost \real r1 = (Integer)10;
      //@ assert r1 == 10.0;
      //@ ghost \real r2 = Long.valueOf(10L);
      //@ assert r2 == 10.0;
      //@ ghost \real r3 = Short.valueOf((short)10);
      //@ assert r3 == 10.0;
      //@ ghost \real r4 = Byte.valueOf((byte)10);
      //@ assert r4 == 10.0;
      //@ ghost \real r5 = Character.valueOf((char)10);
      //@ assert r5 == 10.0;
      //@ ghost \real r6 = (Double)10.0;
      //@ assert r5 == 10.0;
  }
  
  // Just testing these combinations (to make sure that the relevant range assumptions are implicitly applied)
  // Should not be different for the other primitive types.
  public static void p1(short s) {
      //@ ghost var ss = \real.of(s).shortValue();
  }
  public static void p2(short s) {
      //@ ghost var ss = (short)\real.of(s);
  }
  public static void p3(short s) {
      //@ ghost var ss = ((\real)s).shortValue();
  }
  public static void p4(short s) {
      //@ ghost var ss = (short)(\real)s;
  }

  //@ code_java_math spec_java_math
  public static void j0() {
      //@ ghost \real z = (\real)50;
      //@ check (byte)(z+Byte.MAX_VALUE) == -79;
  }
  //@ code_java_math spec_java_math
  public static void j1() {
      //@ ghost \real z = (\real)50;
      //@ check (short)(z+Short.MAX_VALUE) == -32719;
  }
  //@ code_java_math spec_java_math
  public static void j2() {
      //@ ghost \real z = (\real)50;
      //@ check (char)(z+2*Character.MAX_VALUE) == 48;
  }
  //@ code_java_math spec_java_math
  public static void j3() {
      //@ ghost \real z = (\real)50;
      //@ check (int)(z+Integer.MAX_VALUE) == Integer.MAX_VALUE;
  }
  //@ code_java_math spec_java_math
  public static void j4() {
      //@ ghost \real z = (\real)50;
      //@ check (long)(z+Long.MAX_VALUE) == Long.MAX_VALUE;
  }
  //@ code_bigint_math spec_bigint_math
  public static void b0() {
      //@ ghost \real z = (\real)50;
      //@ check (byte)(z+Byte.MAX_VALUE) == -79;
  }
  //@ code_bigint_math spec_bigint_math
  public static void b1() {
      //@ ghost \real z = (\real)50;
      //@ check (short)(z+Short.MAX_VALUE) == -32719;
  }
  //@ code_bigint_math spec_bigint_math
  public static void b2() {
      //@ ghost \real z = (\real)50;
      //@ check (char)(z+2*Character.MAX_VALUE) == 48;
  }
  //@ code_bigint_math spec_bigint_math
  public static void b3() {
      //@ ghost \real z = (\real)50;
      //@ check (int)(z+Integer.MAX_VALUE) == Integer.MAX_VALUE;
  }
  //@ code_bigint_math spec_bigint_math
  public static void b4() {
      //@ ghost \real z = (\real)50;
      //@ check (long)(z+Long.MAX_VALUE) == Long.MAX_VALUE;
  }
  //@ code_java_math spec_java_math
  public static void f0() {
      //@ ghost \real r = (\real)27/10;
      //@ check (int)r == 2;
      //@ check (int)(-r) == -2;
  }
  //@ code_java_math spec_java_math
  public static void w0() {
      //@ ghost \real z = (\real)50;
      //@ check (int)(z+Integer.MAX_VALUE) == Integer.MAX_VALUE;
      //@ check (int)(\bigint)(z+Integer.MAX_VALUE) == -2147483599;
  }
  public static void s0() {
      //@ ghost \real z = (\real)50;
      //@ check (byte)(z+Byte.MAX_VALUE) == -79;
  }
  public static void s1() {
      //@ ghost \real z = (\real)50;
      //@ check (short)(z+Short.MAX_VALUE) == -32719;
  }
  public static void s2() {
      //@ ghost \real z = (\real)50;
      //@ check (char)(z+2*Character.MAX_VALUE) == 48;
  }
  public static void s3() {
      //@ ghost \real z = (\real)50;
      //@ check (int)(z+Integer.MAX_VALUE) == Integer.MAX_VALUE;
  }
  public static void s4() {
      //@ ghost \real z = (\real)50;
      //@ check (long)(z+Long.MAX_VALUE) == Long.MAX_VALUE;
  }
}
