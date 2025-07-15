public class Tcasts {
  public static void main(String... args) { //-ESC@ set System.out.println("CASTS");
      m1(); m2(); m3(); m4(); m5(); m6(); m7(); m8(); m9(); p1((short)0); p2((short)0); p3((short)0); p4((short)0);
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
}
