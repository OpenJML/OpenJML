import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;

// Methods that return a new object are not allowed in assertions, so results go into locals first
public class TestBigDecimal {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        constants();
        construct();
        arithmetic();
        scales();
        movePoint();
        strip();
        comparison();
        conversions();
        division();
        exceptions();
        System.out.println("DONE");
    }

    public static void constants() {
        //@ assert BigDecimal.ZERO.signum() == 0 && BigDecimal.ZERO.scale() == 0;
        //@ assert BigDecimal.ONE.intValue() == 1;
        //@ assert BigDecimal.TEN.longValue() == 10L;
    }

    public static void construct() {
        BigDecimal a = BigDecimal.valueOf(1234, 2);  // 12.34
        //@ assert a.scale() == 2;
        BigInteger u = a.unscaledValue();
        //@ assert u.intValue() == 1234;
        //@ assert a.precision() == 4;
        BigDecimal b = new BigDecimal(BigInteger.valueOf(-5), 1);  // -0.5
        //@ assert b.signum() == -1 && b.scale() == 1;
        BigDecimal c = new BigDecimal(7);
        //@ assert c.scale() == 0 && c.intValue() == 7;
        BigDecimal d = new BigDecimal(0.5);
        BigDecimal half = BigDecimal.valueOf(5, 1);
        //@ assert d.compareTo(half) == 0;
    }

    public static void arithmetic() {
        BigDecimal a = BigDecimal.valueOf(125, 2);  // 1.25
        BigDecimal b = BigDecimal.valueOf(5, 1);    // 0.5
        BigDecimal r = a.add(b);                    // 1.75
        //@ assert r.scale() == 2;
        BigInteger u = r.unscaledValue();
        //@ assert u.intValue() == 175;
        r = a.subtract(b);                          // 0.75
        u = r.unscaledValue();
        //@ assert r.scale() == 2 && u.intValue() == 75;
        r = a.multiply(b);                          // 0.625
        u = r.unscaledValue();
        //@ assert r.scale() == 3 && u.intValue() == 625;
        r = b.negate();
        //@ assert r.signum() == -1 && r.scale() == 1;
        BigDecimal r2 = r.abs();
        //@ assert r2.equals(b);
        r = b.pow(2);                               // 0.25
        u = r.unscaledValue();
        //@ assert r.scale() == 2 && u.intValue() == 25;
        r = b.plus();
        //@ assert r == b;
    }

    public static void scales() {
        BigDecimal a = BigDecimal.valueOf(15, 1);   // 1.5
        BigDecimal r = a.setScale(3);               // 1.500
        BigInteger u = r.unscaledValue();
        //@ assert r.scale() == 3 && u.intValue() == 1500;
        r = a.setScale(0, RoundingMode.DOWN);       // 1
        u = r.unscaledValue();
        //@ assert r.scale() == 0 && u.intValue() == 1;
    }

    public static void movePoint() {
        BigDecimal a = BigDecimal.valueOf(15, 1);   // 1.5
        BigDecimal r = a.movePointLeft(2);          // 0.015
        BigInteger u = r.unscaledValue();
        //@ assert r.scale() == 3 && u.intValue() == 15;
        r = a.movePointRight(3);                    // 1500
        u = r.unscaledValue();
        //@ assert r.scale() == 0 && u.intValue() == 1500;
        r = a.scaleByPowerOfTen(2);                 // 15E+1
        u = r.unscaledValue();
        //@ assert r.scale() == -1 && u.intValue() == 15;
        r = a.ulp();
        u = r.unscaledValue();
        //@ assert r.scale() == 1 && u.intValue() == 1;
    }

    public static void strip() {
        BigDecimal a = BigDecimal.valueOf(1500, 3);  // 1.500
        BigDecimal s = a.stripTrailingZeros();       // 1.5
        //@ assert s.compareTo(a) == 0;
    }

    public static void comparison() {
        BigDecimal a = BigDecimal.valueOf(20, 1);   // 2.0
        BigDecimal b = BigDecimal.valueOf(2);       // 2
        // equal values, different scales
        //@ assert a.compareTo(b) == 0;
        //@ assert !a.equals(b);
        BigDecimal a2 = BigDecimal.valueOf(20, 1);
        //@ assert a.equals(a2);
        //@ assert !a.equals("2.0") && !a.equals(null);
        BigDecimal c = BigDecimal.valueOf(-1);
        //@ assert c.compareTo(a) == -1 && a.compareTo(c) == 1;
        BigDecimal m = a.min(c);
        //@ assert m == c;
        m = a.max(c);
        //@ assert m == a;
    }

    public static void conversions() {
        BigDecimal a = BigDecimal.valueOf(-275, 2);  // -2.75
        BigInteger i = a.toBigInteger();
        //@ assert i.intValue() == -2;
        //@ assert a.intValue() == -2;
        BigDecimal b = BigDecimal.valueOf(300, 1);   // 30.0
        i = b.toBigIntegerExact();
        //@ assert i.intValue() == 30;
        //@ assert b.intValueExact() == 30;
        //@ assert b.longValueExact() == 30L;
        //@ assert b.byteValueExact() == 30;
    }

    public static void division() {
        BigDecimal a = BigDecimal.valueOf(7);
        BigDecimal b = BigDecimal.valueOf(2);
        BigDecimal q = a.divideToIntegralValue(b);
        BigInteger u = q.unscaledValue();
        //@ assert q.scale() == 0 && u.intValue() == 3;
        BigDecimal r = a.remainder(b);
        u = r.unscaledValue();
        //@ assert r.scale() == 0 && u.intValue() == 1;
        BigDecimal x = a.divide(b, 1, RoundingMode.HALF_UP);  // 3.5
        //@ assert x.scale() == 1;
    }

    public static void exceptions() {
        try {
            BigDecimal.ONE.divide(BigDecimal.ZERO);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            BigDecimal.valueOf(15, 1).setScale(0);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            BigDecimal.valueOf(15, 1).intValueExact();
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            BigDecimal.ONE.pow(-1);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            new BigDecimal(Double.NaN);
            //@ unreachable;
        } catch (NumberFormatException e) {
        }
    }
}
