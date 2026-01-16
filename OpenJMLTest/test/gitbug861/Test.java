// The problem here is that the initialization is a compiler-constant
// and consequently there is no check for overflow in either --esc or --rac
public class Test {
    public final static short DECIMAL_OVERFLOW = (short)40000;

    public static void main(String ... args) { }
}
