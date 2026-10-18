// Casts between Java integral types narrow as Java does -- the value modulo 2^n, in the type's range -- and
// char is unsigned (#1018): (char) of an int, byte or short; (short) and (byte) of a char; a char widened to int.
//   javaMode: Java math: no warnings
//   safeMode: Safe math: an out-of-range argument is warned about (here: the negative byte and short, and the
//             char 65535 cast to short and to byte)
// Run by ESC (escfiles3.gitbug1018; escfiles3.gitbug1018bv with the bit-vector encoding) and by RAC
// (racfiles.gitbug1018rac). Casts of \bigint values: test/jmlbigintCasts (ESC) and test/jmlbigint (RAC).
public class Narrow {
    //@ code_java_math spec_java_math
    public static void javaMode() {
        int x = 65535;
        char c = (char)x;
        //@ check c == 65535;
        byte y = -1;
        char d = (char)y;
        //@ check d == 65535;
        short z = -1;
        char e = (char)z;
        //@ check e == 65535;
        short s = (short)c;
        //@ check s == -1;
        byte b = (byte)c;
        //@ check b == -1;
        int w = c;
        //@ check w == 65535;
    }

    //@ code_safe_math spec_safe_math
    public static void safeMode() {
        int x = 65535;
        char c = (char)x;
        //@ check c == 65535;
        byte y = -1;
        char d = (char)y;           // warned about
        //@ check d == 65535;
        short z = -1;
        char e = (char)z;           // warned about
        //@ check e == 65535;
        short s = (short)c;         // warned about
        //@ check s == -1;
        byte b = (byte)c;           // warned about
        //@ check b == -1;
        int w = c;
        //@ check w == 65535;
    }

    // In-range casts between char and short or byte are not warned about (#1045)
    //@ code_safe_math spec_safe_math
    public static void inRange() {
        char c = 'a';
        byte b = (byte)c;
        //@ check b == 97;
        short s = (short)c;
        //@ check s == 97;
        char m = 127;
        byte bm = (byte)m;
        //@ check bm == 127;
        char n = 32767;
        short sn = (short)n;
        //@ check sn == 32767;
        char o = 128;
        byte bo = (byte)o;          // warned about
        byte y = 5;
        char cy = (char)y;
        //@ check cy == 5;
        short z = 300;
        char cz = (char)z;
        //@ check cz == 300;
    }

    public static void main(String... args) {
        javaMode();
        safeMode();
        System.out.println("DONE");
    }
}
