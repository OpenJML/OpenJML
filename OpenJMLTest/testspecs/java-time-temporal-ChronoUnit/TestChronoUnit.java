import java.time.temporal.ChronoUnit;

public class TestChronoUnit {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        constants();
        timeBased();
        dateBased();
        System.out.println("DONE");
    }

    public static void constants() {
        //@ assert ChronoUnit.NANOS != ChronoUnit.SECONDS && ChronoUnit.DAYS != ChronoUnit.FOREVER;
        //@ assert ChronoUnit.NANOS.ordinal() == 0 && ChronoUnit.FOREVER.ordinal() == 15;
    }

    public static void timeBased() {
        //@ assert ChronoUnit.NANOS.isTimeBased() && !ChronoUnit.NANOS.isDateBased() && !ChronoUnit.NANOS.isDurationEstimated();
        //@ assert ChronoUnit.HALF_DAYS.isTimeBased() && !ChronoUnit.HALF_DAYS.isDurationEstimated();
    }

    public static void dateBased() {
        //@ assert ChronoUnit.DAYS.isDateBased() && !ChronoUnit.DAYS.isTimeBased() && ChronoUnit.DAYS.isDurationEstimated();
        //@ assert ChronoUnit.MILLENNIA.isDateBased() && ChronoUnit.ERAS.isDateBased();
        //@ assert !ChronoUnit.FOREVER.isDateBased() && !ChronoUnit.FOREVER.isTimeBased() && ChronoUnit.FOREVER.isDurationEstimated();
    }
}
