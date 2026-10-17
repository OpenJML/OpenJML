// A cast whose argument may be out of range, followed by an assertion that holds only if it was in range:
// --arithmetic-failure says what a failed range check of a cast means for the code after it, as it does for
// arithmetic operations (#1018). Safe math (the default for code).
//   hard:  the cast is reported; its argument is assumed in range afterwards, so the assertion holds
//   soft:  the cast is reported; the value is narrowed as Java does, so the assertion may fail
//   quiet: the cast is not reported; its argument is assumed in range, so the assertion holds
import org.jmlspecs.annotation.Options;
public class Modes {
    //@ requires 0 <= x;
    @Options("--arithmetic-failure=hard")
    public static void hard(long x) {
        int i = (int)x;
        //@ assert i >= 0;
    }

    //@ requires 0 <= x;
    @Options("--arithmetic-failure=soft")
    public static void soft(long x) {
        int i = (int)x;
        //@ assert i >= 0;
    }

    //@ requires 0 <= x;
    @Options("--arithmetic-failure=quiet")
    public static void quiet(long x) {
        int i = (int)x;
        //@ assert i >= 0;
    }
}
