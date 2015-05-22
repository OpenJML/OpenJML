public class BoxingTests {
    public static Integer incr_test() {
        Integer x = new Integer(0);
        x++;
        return x;
    }

    public static Boolean and_test() {
        Boolean b = Boolean.TRUE;
        b &= false;
        return b;
    }
}