// With the bit-vector encoding, char operands of a comparison are compared as unsigned values, as Java
// promotes them to int (#1020): two chars, and a char with a negative byte or short. No warnings expected.
// Run by ESC (escfiles3.gitbug1020, --esc-bv=true); escfiles3.gitbug1018bv covers Safe-mode casts of char.
public class CharCompare {
    //@ code_java_math spec_java_math
    public static void m() {
        char c = '￿';
        char d = 'a';
        //@ check c > 'a';
        //@ check c >= d;
        //@ check d < c;
        //@ check d <= c;
        //@ check c != d;
        byte b = -1;
        //@ check b < c;
        //@ check b < d;
        short s = -1;
        //@ check s < c;
        //@ check c > s;
        //@ check c == 65535;
    }
}
