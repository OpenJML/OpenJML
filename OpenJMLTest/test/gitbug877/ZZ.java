// This crashes when compiled with --rac; an equivalent using old-style 'case ...:... break;' does not crash
public class ZZ {
  public static void main(String... args) {
    //@ ghost \bigint z = \bigint.one*10;
    for (int i = 0; i<5; i++) {
        switch (i) { 
            case 0 -> { /*@ show (byte)(z+Byte.MAX_VALUE); */} 
            case 1 -> { /*@ show (short)(z+Short.MAX_VALUE); */}
            case 2 -> { /*@ show (char)(z+Character.MAX_VALUE); */}
            case 3 -> { /*@ show (int)(z+Integer.MAX_VALUE); */}
            default -> { /*@ show (long)(z+Long.MAX_VALUE); */}
         }
    } 
  }
}
