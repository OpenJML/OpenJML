import java.time.DateTimeException;
import java.time.Month;
import java.time.temporal.ChronoField;

public class TestMonth {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        values();
        arithmetic();
        lengths();
        exceptions();
        System.out.println("DONE");
    }

    public static void values() {
        //@ assert Month.JANUARY.getValue() == 1;
        //@ assert Month.DECEMBER.getValue() == 12;
        Month m = Month.of(6);
        //@ assert m == Month.JUNE;
        //@ assert Month.from(m) == m;
        //@ assert m.get(ChronoField.MONTH_OF_YEAR) == 6;
        //@ assert m.isSupported(ChronoField.MONTH_OF_YEAR) && !m.isSupported(ChronoField.DAY_OF_WEEK);
    }

    public static void arithmetic() {
        Month m = Month.NOVEMBER.plus(3);
        //@ assert m == Month.FEBRUARY;
        Month n = Month.MARCH.minus(14);
        //@ assert n == Month.JANUARY;
        Month q = Month.AUGUST.firstMonthOfQuarter();
        //@ assert q == Month.JULY;
    }

    public static void lengths() {
        //@ assert Month.FEBRUARY.length(true) == 29 && Month.FEBRUARY.length(false) == 28;
        //@ assert Month.APRIL.length(true) == 30 && Month.JULY.length(false) == 31;
        //@ assert Month.FEBRUARY.minLength() == 28 && Month.FEBRUARY.maxLength() == 29;
        //@ assert Month.MARCH.firstDayOfYear(false) == 60 && Month.MARCH.firstDayOfYear(true) == 61;
        //@ assert Month.DECEMBER.firstDayOfYear(true) == 336;
    }

    public static void exceptions() {
        try {
            Month.of(13);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
    }
}
