import java.math.BigInteger;

// Methods that return a new BigInteger are not allowed in assertions, so results go into locals first
public class TestBigInteger {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        constants();
        arithmetic();
        division();
        powAndSqrt();
        gcd();
        modular();
        shifts();
        bits();
        comparison();
        exact();
        exceptions();
        System.out.println("DONE");
    }

    public static void constants() {
        //@ assert BigInteger.ZERO.signum() == 0;
        //@ assert BigInteger.ONE.intValue() == 1;
        //@ assert BigInteger.TWO.intValue() == 2;
        //@ assert BigInteger.TEN.longValue() == 10L;
        BigInteger a = BigInteger.valueOf(-5);
        //@ assert a.signum() == -1;
        //@ assert a.intValue() == -5;
    }

    public static void arithmetic() {
        BigInteger a = BigInteger.valueOf(7);
        BigInteger b = BigInteger.valueOf(-3);
        BigInteger r = a.add(b);
        //@ assert r.intValue() == 4;
        r = a.subtract(b);
        //@ assert r.intValue() == 10;
        r = a.multiply(b);
        //@ assert r.intValue() == -21;
        r = a.parallelMultiply(b);
        //@ assert r.intValue() == -21;
        r = b.negate();
        //@ assert r.intValue() == 3;
        r = b.abs();
        //@ assert r.intValue() == 3;
        r = a.abs();
        //@ assert r == a;
        BigInteger max = BigInteger.valueOf(Long.MAX_VALUE);
        BigInteger big = max.add(BigInteger.ONE);
        //@ assert big.signum() == 1;
        //@ assert big.compareTo(max) == 1;
    }

    public static void division() {
        BigInteger a = BigInteger.valueOf(-7);
        BigInteger b = BigInteger.valueOf(2);
        // Truncation toward zero
        BigInteger q = a.divide(b);
        //@ assert q.intValue() == -3;
        BigInteger r = a.remainder(b);
        //@ assert r.intValue() == -1;
        BigInteger[] qr = a.divideAndRemainder(b);
        //@ assert qr[0].intValue() == -3 && qr[1].intValue() == -1;
        // mod is non-negative
        BigInteger m = a.mod(b);
        //@ assert m.intValue() == 1;
    }

    public static void powAndSqrt() {
        BigInteger three = BigInteger.valueOf(3);
        BigInteger p = three.pow(0);
        //@ assert p.equals(BigInteger.ONE);
        p = three.pow(4);
        //@ assert p.intValue() == 81;
        p = BigInteger.valueOf(-2).pow(3);
        //@ assert p.intValue() == -8;
        BigInteger seventeen = BigInteger.valueOf(17);
        BigInteger s = seventeen.sqrt();
        //@ assert s.intValue() == 4;
        BigInteger[] sr = seventeen.sqrtAndRemainder();
        //@ assert sr[0].intValue() == 4 && sr[1].intValue() == 1;
    }

    public static void gcd() {
        BigInteger g = BigInteger.valueOf(12).gcd(BigInteger.ZERO);
        //@ assert g.intValue() == 12;
        g = BigInteger.ZERO.gcd(BigInteger.valueOf(-5));
        //@ assert g.intValue() == 5;
        BigInteger twelve = BigInteger.valueOf(12);
        g = twelve.gcd(BigInteger.valueOf(18));
        //@ assert g.signum() == 1;
        BigInteger r = twelve.remainder(g);
        //@ assert r.signum() == 0;
    }

    public static void modular() {
        BigInteger m = BigInteger.valueOf(7);
        BigInteger three = BigInteger.valueOf(3);
        BigInteger r = three.modPow(BigInteger.ZERO, m);
        //@ assert r.intValue() == 1;
        r = three.modPow(BigInteger.valueOf(5), m);
        //@ assert 0 <= r.intValue() && r.intValue() < 7;
        BigInteger inv = three.modInverse(m);
        //@ assert inv.intValue() == 5;
    }

    public static void shifts() {
        BigInteger a = BigInteger.valueOf(-5);
        BigInteger r = a.shiftLeft(2);
        //@ assert r.intValue() == -20;
        // Floor division
        r = a.shiftRight(1);
        //@ assert r.intValue() == -3;
        r = a.shiftLeft(-1);
        //@ assert r.intValue() == -3;
        r = BigInteger.valueOf(5).shiftRight(1);
        //@ assert r.intValue() == 2;
        r = a.not();
        //@ assert r.intValue() == 4;
    }

    public static void bits() {
        BigInteger five = BigInteger.valueOf(5);
        //@ assert five.testBit(0) && !five.testBit(1) && five.testBit(2);
        BigInteger r = five.setBit(1);
        //@ assert r.intValue() == 7;
        r = five.clearBit(0);
        //@ assert r.intValue() == 4;
        r = five.flipBit(3);
        //@ assert r.intValue() == 13;
        //@ assert five.getLowestSetBit() == 0;
        //@ assert BigInteger.ZERO.getLowestSetBit() == -1;
        //@ assert five.bitLength() == 3;
        //@ assert BigInteger.ZERO.bitLength() == 0;
    }

    public static void comparison() {
        BigInteger a = BigInteger.valueOf(2);
        BigInteger b = BigInteger.valueOf(9);
        //@ assert a.compareTo(b) == -1 && b.compareTo(a) == 1 && a.compareTo(a) == 0;
        BigInteger r = a.min(b);
        //@ assert r.equals(a);
        r = a.max(b);
        //@ assert r.equals(b);
        //@ assert !a.equals(b) && !a.equals("2") && !a.equals(null);
        //@ assert a.equals(BigInteger.TWO);
        //@ assert BigInteger.ONE.isProbablePrime(0);
        //@ assert !BigInteger.ONE.isProbablePrime(10);
    }

    public static void exact() {
        BigInteger a = BigInteger.valueOf(-128);
        //@ assert a.byteValueExact() == -128;
        a = BigInteger.valueOf(300);
        //@ assert a.shortValueExact() == 300;
        a = BigInteger.valueOf(Integer.MIN_VALUE);
        //@ assert a.intValueExact() == Integer.MIN_VALUE;
        a = BigInteger.valueOf(Long.MAX_VALUE);
        //@ assert a.longValueExact() == Long.MAX_VALUE;
    }

    public static void exceptions() {
        try {
            BigInteger.ONE.divide(BigInteger.ZERO);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            BigInteger.valueOf(128).byteValueExact();
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            BigInteger.valueOf(Long.MAX_VALUE).add(BigInteger.ONE).longValueExact();
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            BigInteger.TEN.pow(-1);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            BigInteger.ONE.mod(BigInteger.ZERO);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            BigInteger.valueOf(-4).sqrt();
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            BigInteger.ONE.testBit(-1);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
    }
}
