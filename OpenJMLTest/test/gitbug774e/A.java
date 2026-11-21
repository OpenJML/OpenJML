// .jml initializers of compile-time constants are compared with the constant values (#774):
// the first group matches, the second does not
public class A {
    static final int OK1 = 5;
    static final int OK2 = 2+3;
    static final int OK3 = -1;
    static final double OK4 = Double.NaN;
    static final String OK5 = "a" + "bc";
    final long OK6 = 7L;

    static final int E1 = 5;
    static final int E2 = 2+3;
    static final boolean E3 = true;
    static final char E4 = 'a';
    static final double E5 = 0.0;
    static final String E6 = "abc";
    final long E7 = 7L;
    public A() {}
}
