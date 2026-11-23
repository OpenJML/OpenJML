import java.time.Duration;
import java.time.temporal.ChronoUnit;

public class TestDuration {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        normalize();
        predicates();
        arithmetic();
        arithmeticNegative();
        conversions();
        parts();
        comparison();
        overflow();
        System.out.println("DONE");
    }

    public static void construct() {
        //@ assert Duration.ZERO.isZero();
        Duration d = Duration.ofMinutes(3);
        //@ assert d.getSeconds() == 180 && d.getNano() == 0;
        Duration e = Duration.ofDays(2);
        //@ assert e.getSeconds() == 172800;
        Duration f = Duration.ofMillis(1500);
        //@ assert f.getSeconds() == 1 && f.getNano() == 500_000_000;
    }

    public static void normalize() {
        Duration d = Duration.ofSeconds(3, -1);
        //@ assert d.getSeconds() == 2 && d.getNano() == 999_999_999;
        Duration e = Duration.ofMillis(-1);
        //@ assert e.getSeconds() == -1 && e.getNano() == 999_000_000;
        Duration f = Duration.ofNanos(-2_500_000_000L);
        //@ assert f.getSeconds() == -3 && f.getNano() == 500_000_000;
    }

    public static void predicates() {
        Duration d = Duration.ofNanos(1);
        //@ assert d.isPositive() && !d.isZero() && !d.isNegative();
        Duration e = Duration.ofNanos(-1);
        //@ assert e.isNegative() && !e.isPositive();
        //@ assert e.get(ChronoUnit.SECONDS) == -1 && e.get(ChronoUnit.NANOS) == 999_999_999;
    }

    public static void arithmetic() {
        Duration d = Duration.ofSeconds(10, 600_000_000);
        Duration e = d.plus(Duration.ofSeconds(0, 500_000_000));
        //@ assert e.getSeconds() == 11 && e.getNano() == 100_000_000;
        Duration f = d.plusMillis(400);
        //@ assert f.getSeconds() == 11 && f.getNano() == 0;
        Duration g = d.plusHours(1);
        //@ assert g.getSeconds() == 3610;
    }

    public static void arithmeticNegative() {
        Duration d = Duration.ofSeconds(1);
        Duration e = d.minus(Duration.ofSeconds(2, 1));
        //@ assert e.getSeconds() == -2 && e.getNano() == 999_999_999;
        Duration f = e.negated();
        //@ assert f.getSeconds() == 1 && f.getNano() == 1;
        Duration g = e.abs();
        boolean gf = g.equals(f);
        //@ assert gf;
        Duration h = d.minusNanos(1);
        //@ assert h.getSeconds() == 0 && h.getNano() == 999_999_999;
    }

    public static void conversions() {
        Duration d = Duration.ofSeconds(90061, 5_000_000);
        //@ assert d.toDays() == 1 && d.toHours() == 25 && d.toMinutes() == 1501;
        //@ assert d.toMillis() == 90_061_005L;
        //@ assert d.toNanos() == 90_061_005_000_000L;
        Duration e = Duration.ofNanos(-1_500_000);
        //@ assert e.toMillis() == -1;
    }

    public static void parts() {
        Duration d = Duration.ofSeconds(90061, 5_000_000);
        //@ assert d.toDaysPart() == 1 && d.toHoursPart() == 1 && d.toMinutesPart() == 1 && d.toSecondsPart() == 1;
        //@ assert d.toMillisPart() == 5 && d.toNanosPart() == 5_000_000;
    }

    public static void comparison() {
        Duration a = Duration.ofSeconds(1, 5);
        Duration b = Duration.ofSeconds(1, 7);
        //@ assert a.compareTo(b) < 0 && b.compareTo(a) > 0 && a.compareTo(a) == 0;
        boolean e = !a.equals(b) && a.equals(Duration.ofNanos(1_000_000_005L));
        //@ assert e;
        boolean w = a.withNanos(7).equals(b);
        //@ assert w;
        //@ assert a.withSeconds(4).getSeconds() == 4 && a.withSeconds(4).getNano() == 5;
    }

    public static void overflow() {
        Duration max = Duration.ofSeconds(Long.MAX_VALUE, 999_999_999);
        try {
            max.plusNanos(1);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            Duration.ofDays(Long.MAX_VALUE / 1000);
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            Duration.ofSeconds(Long.MIN_VALUE).negated();
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
        try {
            max.toNanos();
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
    }
}
