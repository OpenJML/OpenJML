import java.time.DateTimeException;
import java.time.Instant;

public class TestInstant {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        constants();
        construct();
        arithmetic();
        millis();
        comparison();
        limits();
        System.out.println("DONE");
    }

    public static void constants() {
        //@ assert Instant.EPOCH.getEpochSecond() == 0 && Instant.EPOCH.getNano() == 0;
        //@ assert Instant.MAX.getNano() == 999_999_999;
        //@ assert Instant.MIN.isBefore(Instant.EPOCH) && Instant.MAX.isAfter(Instant.EPOCH);
    }

    public static void construct() {
        Instant a = Instant.ofEpochSecond(100, -1);
        //@ assert a.getEpochSecond() == 99 && a.getNano() == 999_999_999;
        Instant b = Instant.ofEpochMilli(-1);
        //@ assert b.getEpochSecond() == -1 && b.getNano() == 999_000_000;
        Instant c = Instant.ofEpochSecond(7);
        //@ assert c.getEpochSecond() == 7 && c.getNano() == 0;
    }

    public static void arithmetic() {
        Instant a = Instant.ofEpochSecond(10, 900_000_000);
        Instant b = a.plusMillis(200);
        //@ assert b.getEpochSecond() == 11 && b.getNano() == 100_000_000;
        Instant c = a.minusNanos(900_000_001);
        //@ assert c.getEpochSecond() == 9 && c.getNano() == 999_999_999;
        Instant d = a.plusSeconds(-20);
        //@ assert d.getEpochSecond() == -10 && d.getNano() == 900_000_000;
    }

    public static void millis() {
        Instant a = Instant.ofEpochSecond(-1, 500_000);
        //@ assert a.toEpochMilli() == -1000;
        Instant b = Instant.ofEpochSecond(3, 999_999_999);
        //@ assert b.toEpochMilli() == 3999;
    }

    public static void comparison() {
        Instant a = Instant.ofEpochSecond(5, 1);
        Instant b = Instant.ofEpochSecond(5, 2);
        //@ assert a.compareTo(b) < 0 && a.isBefore(b) && !a.isAfter(b);
        boolean e = a.equals(Instant.ofEpochSecond(4, 1_000_000_001L)) && !a.equals(b);
        //@ assert e;
    }

    public static void limits() {
        try {
            Instant.MAX.plusNanos(1);
            //@ unreachable;
        } catch (DateTimeException | ArithmeticException e) {
        }
        try {
            Instant.ofEpochSecond(Long.MAX_VALUE);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
        try {
            Instant.MAX.toEpochMilli();
            //@ unreachable;
        } catch (ArithmeticException e) {
        }
    }
}
