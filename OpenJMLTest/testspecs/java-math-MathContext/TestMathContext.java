import java.math.MathContext;
import java.math.RoundingMode;

public class TestMathContext {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        constants();
        construct();
        equality();
        exceptions();
        System.out.println("DONE");
    }

    public static void constants() {
        //@ assert MathContext.UNLIMITED.getPrecision() == 0;
        //@ assert MathContext.UNLIMITED.getRoundingMode() == RoundingMode.HALF_UP;
        //@ assert MathContext.DECIMAL32.getPrecision() == 7;
        //@ assert MathContext.DECIMAL64.getPrecision() == 16;
        //@ assert MathContext.DECIMAL128.getPrecision() == 34;
        //@ assert MathContext.DECIMAL128.getRoundingMode() == RoundingMode.HALF_EVEN;
    }

    public static void construct() {
        MathContext a = new MathContext(5);
        //@ assert a.getPrecision() == 5 && a.getRoundingMode() == RoundingMode.HALF_UP;
        MathContext b = new MathContext(3, RoundingMode.FLOOR);
        //@ assert b.getPrecision() == 3 && b.getRoundingMode() == RoundingMode.FLOOR;
        MathContext c = new MathContext("precision=7 roundingMode=HALF_EVEN");
        //@ assert c.getPrecision() >= 0;
    }

    public static void equality() {
        MathContext a = new MathContext(7, RoundingMode.HALF_EVEN);
        //@ assert a.equals(MathContext.DECIMAL32);
        MathContext b = new MathContext(7);
        //@ assert !b.equals(MathContext.DECIMAL32);
        //@ assert !a.equals("precision=7");
        //@ assert a.hashCode() == MathContext.DECIMAL32.hashCode();
    }

    public static void exceptions() {
        try {
            new MathContext(-1);
            //@ unreachable;
        } catch (IllegalArgumentException e) {
        }
        try {
            new MathContext(2, null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
        try {
            new MathContext("bad");
            //@ unreachable;
        } catch (IllegalArgumentException e) {
        }
    }
}
