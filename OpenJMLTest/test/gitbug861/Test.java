// The initializer is a compile-time constant with an out-of-range cast (#861): RAC reports it, and
// ESC reports it in <clinit> (#1152)
public class Test {
    public final static short DECIMAL_OVERFLOW = (short)40000;

    public static void main(String ... args) { }
}
