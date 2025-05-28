public class Test {
    static {  } 
    private static int m() { return 0; }
    public static int DECIMAL_OVERFLOW   = m(); // FIXME - this causes a translation error -- needs the m() and the static{}

    public static void main(String ... args) { }
}
