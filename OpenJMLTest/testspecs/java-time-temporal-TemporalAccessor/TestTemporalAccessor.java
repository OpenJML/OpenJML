import java.time.DateTimeException;
import java.time.DayOfWeek;
import java.time.Month;
import java.time.temporal.ChronoField;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalField;

// TemporalAccessor promises only that its queries are pure; these tests call them through the interface type.
public class TestTemporalAccessor {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        repeatable(DayOfWeek.FRIDAY, ChronoField.DAY_OF_WEEK);
        repeatable(Month.MAY, ChronoField.DAY_OF_WEEK);
        repeatableGet(Month.MAY, ChronoField.MONTH_OF_YEAR);
        System.out.println("DONE");
    }

    // A query returns the same result when asked twice
    public static void repeatable(TemporalAccessor t, TemporalField f) {
        boolean a = t.isSupported(f);
        boolean b = t.isSupported(f);
        //@ assert a == b;
        try {
            long x = t.getLong(f);
            long y = t.getLong(f);
            //@ assert x == y;
        } catch (DateTimeException | ArithmeticException e) {
        }
    }

    public static void repeatableGet(TemporalAccessor t, TemporalField f) {
        try {
            int x = t.get(f);
            int y = t.get(f);
            //@ assert x == y;
        } catch (DateTimeException | ArithmeticException e) {
        }
    }
}
