import java.time.DateTimeException;
import java.time.LocalTime;

public class TestLocalTime {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        constants();
        construct();
        ofDay();
        plus();
        wrap();
        minus();
        comparison();
        exceptions();
        System.out.println("DONE");
    }

    public static void constants() {
        //@ assert LocalTime.MIDNIGHT.getHour() == 0 && LocalTime.MIDNIGHT.getMinute() == 0;
        //@ assert LocalTime.NOON.getHour() == 12 && LocalTime.NOON.getSecond() == 0;
        //@ assert LocalTime.MAX.getHour() == 23 && LocalTime.MAX.getNano() == 999_999_999;
    }

    public static void construct() {
        LocalTime t = LocalTime.of(13, 45, 20, 7);
        //@ assert t.getHour() == 13 && t.getMinute() == 45 && t.getSecond() == 20 && t.getNano() == 7;
        //@ assert t.toSecondOfDay() == 13 * 3600 + 45 * 60 + 20;
        LocalTime u = LocalTime.of(9, 5);
        //@ assert u.getHour() == 9 && u.getMinute() == 5 && u.getSecond() == 0;
    }

    public static void ofDay() {
        LocalTime t = LocalTime.ofSecondOfDay(3661);
        //@ assert t.getHour() == 1 && t.getMinute() == 1 && t.getSecond() == 1 && t.getNano() == 0;
        LocalTime u = LocalTime.ofNanoOfDay(1_000_000_001L);
        //@ assert u.getSecond() == 1 && u.getNano() == 1 && u.getHour() == 0;
    }

    public static void plus() {
        LocalTime t = LocalTime.of(10, 30);
        LocalTime u = t.plusMinutes(45);
        //@ assert u.getHour() == 11 && u.getMinute() == 15;
        LocalTime v = t.plusSeconds(30);
        //@ assert v.getMinute() == 30 && v.getSecond() == 30;
    }

    public static void wrap() {
        LocalTime t = LocalTime.of(22, 0);
        LocalTime u = t.plusHours(5);
        //@ assert u.getHour() == 3 && u.getMinute() == 0;
        LocalTime v = t.plusHours(-23);
        //@ assert v.getHour() == 23;
        LocalTime w = LocalTime.of(23, 59, 59, 999_999_999).plusNanos(1);
        //@ assert w.toNanoOfDay() == 0;
    }

    public static void minus() {
        LocalTime t = LocalTime.of(0, 10);
        LocalTime u = t.minusMinutes(20);
        //@ assert u.getHour() == 23 && u.getMinute() == 50;
        LocalTime v = t.minusHours(Long.MIN_VALUE);
        //@ assert v.getHour() == 8 && v.getMinute() == 10; // 2^63 % 24 == 8
    }

    public static void comparison() {
        LocalTime a = LocalTime.of(8, 0);
        LocalTime b = LocalTime.of(8, 0, 0, 1);
        //@ assert a.compareTo(b) == -1 && a.isBefore(b) && b.isAfter(a);
        //@ assert a.equals(LocalTime.of(8, 0, 0)) && !a.equals(b) && !a.equals("08:00");
    }

    public static void exceptions() {
        try {
            LocalTime.of(24, 0);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
        try {
            LocalTime.ofSecondOfDay(86400);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
    }
}
