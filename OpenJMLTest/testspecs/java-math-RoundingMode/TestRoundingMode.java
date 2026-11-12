import java.math.BigDecimal;
import java.math.RoundingMode;

public class TestRoundingMode {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        valueOfInt();
        legacyConstants();
        enumMethods();
        badValue();
        System.out.println("DONE");
    }

    public static void valueOfInt() {
        //@ assert RoundingMode.valueOf(0) == RoundingMode.UP;
        //@ assert RoundingMode.valueOf(3) == RoundingMode.FLOOR;
        //@ assert RoundingMode.valueOf(6) == RoundingMode.HALF_EVEN;
        //@ assert RoundingMode.valueOf(7) == RoundingMode.UNNECESSARY;
    }

    @SuppressWarnings("deprecation")
    public static void legacyConstants() {
        //@ assert RoundingMode.valueOf(BigDecimal.ROUND_HALF_UP) == RoundingMode.HALF_UP;
        //@ assert RoundingMode.valueOf(BigDecimal.ROUND_CEILING) == RoundingMode.CEILING;
    }

    public static void enumMethods() {
        RoundingMode m = RoundingMode.HALF_DOWN;
        //@ assert m != RoundingMode.HALF_UP;
        //@ assert m.ordinal() == 5;
        //@ assert RoundingMode.values().length == 8;
    }

    public static void badValue() {
        try {
            RoundingMode.valueOf(8);
            //@ unreachable;
        } catch (IllegalArgumentException e) {
        }
        try {
            RoundingMode.valueOf(-1);
            //@ unreachable;
        } catch (IllegalArgumentException e) {
        }
    }
}
