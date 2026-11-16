import java.time.DayOfWeek;
import java.time.Month;
import java.time.temporal.ChronoField;
import java.time.temporal.TemporalAccessor;

public class TestChronoField {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        constants();
        timeBased();
        dateBased();
        supportedBy(DayOfWeek.MONDAY);
        supportedBy(Month.MAY);
        System.out.println("DONE");
    }

    public static void constants() {
        //@ assert ChronoField.NANO_OF_SECOND.ordinal() == 0 && ChronoField.OFFSET_SECONDS.ordinal() == 29;
        //@ assert ChronoField.DAY_OF_WEEK != ChronoField.MONTH_OF_YEAR;
    }

    public static void timeBased() {
        //@ assert ChronoField.NANO_OF_SECOND.isTimeBased() && !ChronoField.NANO_OF_SECOND.isDateBased();
        //@ assert ChronoField.AMPM_OF_DAY.isTimeBased();
    }

    public static void dateBased() {
        //@ assert ChronoField.DAY_OF_WEEK.isDateBased() && !ChronoField.DAY_OF_WEEK.isTimeBased();
        //@ assert ChronoField.ERA.isDateBased() && ChronoField.YEAR.isDateBased();
        //@ assert !ChronoField.INSTANT_SECONDS.isDateBased() && !ChronoField.INSTANT_SECONDS.isTimeBased();
    }

    // isSupportedBy is specified as the accessor's own isSupported (through TemporalAccessor; cf. #1143)
    public static void supportedBy(TemporalAccessor t) {
        boolean b = ChronoField.DAY_OF_WEEK.isSupportedBy(t);
        //@ assert b == t.isSupported(ChronoField.DAY_OF_WEEK);
    }
}
