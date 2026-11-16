import java.time.DateTimeException;
import java.time.DayOfWeek;
import java.time.temporal.ChronoField;

public class TestDayOfWeek {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        values();
        of();
        arithmetic();
        fields();
        exceptions();
        System.out.println("DONE");
    }

    public static void values() {
        //@ assert DayOfWeek.MONDAY.getValue() == 1;
        //@ assert DayOfWeek.WEDNESDAY.getValue() == 3;
        //@ assert DayOfWeek.SUNDAY.getValue() == 7;
    }

    public static void of() {
        DayOfWeek d = DayOfWeek.of(5);
        //@ assert d == DayOfWeek.FRIDAY;
        //@ assert DayOfWeek.from(d) == d;
    }

    public static void arithmetic() {
        DayOfWeek d = DayOfWeek.SATURDAY.plus(3);
        //@ assert d == DayOfWeek.TUESDAY;
        DayOfWeek e = DayOfWeek.MONDAY.minus(1);
        //@ assert e == DayOfWeek.SUNDAY;
        DayOfWeek f = DayOfWeek.THURSDAY.plus(-15);
        //@ assert f == DayOfWeek.WEDNESDAY;
        DayOfWeek g = DayOfWeek.FRIDAY.plus(Long.MIN_VALUE);
        //@ assert g == DayOfWeek.THURSDAY; // Long.MIN_VALUE % 7 == -1
    }

    public static void fields() {
        //@ assert DayOfWeek.TUESDAY.isSupported(ChronoField.DAY_OF_WEEK);
        //@ assert !DayOfWeek.TUESDAY.isSupported(ChronoField.MONTH_OF_YEAR);
        //@ assert !DayOfWeek.TUESDAY.isSupported(null);
        //@ assert DayOfWeek.TUESDAY.get(ChronoField.DAY_OF_WEEK) == 2;
        //@ assert DayOfWeek.TUESDAY.getLong(ChronoField.DAY_OF_WEEK) == 2;
    }

    public static void exceptions() {
        try {
            DayOfWeek.of(0);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
        try {
            DayOfWeek.of(8);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
    }
}
