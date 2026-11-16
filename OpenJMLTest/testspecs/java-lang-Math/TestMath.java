public class TestMath {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        exact();
        exactOverflow();
        floor();
        floorNegative();
        System.out.println("DONE");
    }

    public static void exact() {
        //@ assert Math.addExact(2, 3) == 5;
        //@ assert Math.subtractExact(2L, 3L) == -1;
        //@ assert Math.multiplyExact(-4L, 5) == -20;
        //@ assert Math.multiplyExact(6, 7) == 42;
        //@ assert Math.incrementExact(Integer.MAX_VALUE - 1) == Integer.MAX_VALUE;
        //@ assert Math.negateExact(-5L) == 5;
        //@ assert Math.toIntExact(-7L) == -7;
    }

    public static void exactOverflow() {
        try {
            Math.addExact(Long.MAX_VALUE, 1L);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            Math.multiplyExact(1L << 40, 1L << 30);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            Math.negateExact(Integer.MIN_VALUE);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            Math.toIntExact(1L << 31);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
    }

    public static void floor() {
        //@ assert Math.floorDiv(7, 2) == 3;
        //@ assert Math.floorMod(7, 2) == 1;
        //@ assert Math.floorDiv(Long.MIN_VALUE, -1L) == Long.MIN_VALUE;
        //@ assert Math.floorMod(10L, 5L) == 0;
    }

    public static void floorNegative() {
        //@ assert Math.floorDiv(-7, 2) == -4;
        //@ assert Math.floorMod(-7, 2) == 1;
        //@ assert Math.floorDiv(7L, -2) == -4;
        //@ assert Math.floorMod(7L, -2) == -1;
        //@ assert Math.floorMod(-1_500_000_000L, 1_000_000_000L) == 500_000_000L;
        try {
            Math.floorMod(3, 0);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
    }
}
