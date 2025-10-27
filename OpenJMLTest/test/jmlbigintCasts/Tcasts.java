public class Tcasts {
    //@ ghost public static \bigint z = \bigint.one*50;
  public static void main(String... args) {
      m1(); m2(); m3(); m4(); m5(); m6(); m7(); m8(); m9();
  }
  
  public static void m0() {
      /*@ show (byte)(z+Byte.MAX_VALUE); */
  }
  public static void m1() {
      /*@ show (short)(z+Short.MAX_VALUE); */
  }
  public static void m2() {
      /*@ show (char)(z+2*Character.MAX_VALUE); */
  }
  public static void m3() {
      /*@ show (int)(z+Integer.MAX_VALUE); */
  }
  public static void m4() {
      /*@ show (long)(z+Long.MAX_VALUE); */
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
}
