// Issue #1019: in RAC, an operand converted within a constant expression (e.g. 49 in Long.MIN_VALUE + 49) was
// given the whole expression's constant type, so it was compiled as that constant: Long.MIN_VALUE + 49 gave 49.
// The printed values must be those javac gives (the expected output was produced by plain javac and java).
public class ConstExpr {
    static final long X = Long.MIN_VALUE;
    static final int I = Integer.MAX_VALUE;
    static long id(long v) { return v; }
    //@ code_java_math spec_java_math
    public static void main(String... a) {
        long v = 7;
        p("1 MIN+49        ", Long.MIN_VALUE + 49);
        p("2 49+MIN        ", 49 + Long.MIN_VALUE);
        p("3 X+49          ", X + 49);
        p("4 49+X          ", 49 + X);
        p("5 I+1L          ", I + 1L);
        p("6 1L+I          ", 1L + I);
        p("7 I*2L          ", I * 2L);
        p("8 MIN-49        ", Long.MIN_VALUE - 49);
        p("9 MIN+49+v      ", Long.MIN_VALUE + 49 + v);
        p("10 v+(MIN+49)   ", v + (Long.MIN_VALUE + 49));
        p("11 id(MIN+49)   ", id(Long.MIN_VALUE + 49));
        p("12 'a'+1L       ", 'a' + 1L);
        p("13 (byte)3+X    ", (byte)3 + X);
        p("14 MIN/7        ", Long.MIN_VALUE / 7);
        p("15 MIN%7        ", Long.MIN_VALUE % 7);
        p("16 MIN<<1+0     ", (Long.MIN_VALUE >> 1) + 0);
        p("17 1.5+MIN      ", (long)(1.5 + Long.MIN_VALUE));
        p("18 v+49         ", v + 49);
        //@ ghost long g = Long.MIN_VALUE + 49;
        //@ show g, 49 + X, I + 1L;
    }
    static void p(String s, long r) { System.out.println(s + r); }
}
