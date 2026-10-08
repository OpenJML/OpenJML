// Casts between Java integral types narrow as Java does -- the value modulo 2^n, in the type's range -- and
// char is unsigned (#1018): (char) of an int, byte or short; (short) and (byte) of a char; a char widened to int.
//   javaMode: Java math: no warnings
//   safeMode: Safe math: an out-of-range argument is warned about (here: the negative byte and short, and the
//             char 65535 cast to short and to byte)
// Run by ESC (escfiles3.gitbug1018; escfiles3.gitbug1018bv with the bit-vector encoding, javaMode only: #1020) and by RAC
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

    public static void main(String... args) {
        javaMode();
        safeMode();
        System.out.println("DONE");
    }
}
