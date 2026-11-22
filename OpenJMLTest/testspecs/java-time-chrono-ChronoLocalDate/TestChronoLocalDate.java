import java.time.LocalDate;
import java.time.chrono.ChronoLocalDate;

// The ChronoLocalDate comparisons agree with the epoch day; these tests call them through the interface type.
public class TestChronoLocalDate {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        ChronoLocalDate a = LocalDate.of(2024, 5, 10);
        ChronoLocalDate b = LocalDate.of(2024, 6, 1);
        order(a, b);
        order(b, a);
        order(a, a);
        equality(a, LocalDate.of(2024, 5, 10));
        equality(a, b);
        equality(a, "x");
        lengths(a);
        System.out.println("DONE");
    }

    public static void order(ChronoLocalDate x, ChronoLocalDate y) {
        boolean after = x.isAfter(y);
        boolean before = x.isBefore(y);
        boolean same = x.isEqual(y);
        //@ assert after == (x.toEpochDay() > y.toEpochDay());
        //@ assert before == (x.toEpochDay() < y.toEpochDay());
        //@ assert same == (x.toEpochDay() == y.toEpochDay());
        //@ assert after || before || same;
        int c = x.compareTo(y);
        //@ assert before ==> c < 0;
        //@ assert after ==> c > 0;
    }

    public static void equality(ChronoLocalDate x, Object o) {
        boolean e = x.equals(o);
        //@ assert e ==> o instanceof ChronoLocalDate && x.toEpochDay() == ((ChronoLocalDate)o).toEpochDay();
        //@ assert !x.equals(null);
    }

    public static void lengths(ChronoLocalDate x) {
        int m = x.lengthOfMonth();
        int y = x.lengthOfYear();
        //@ assert m > 0 && y > 0;
        //@ assert x.toEpochDay() == x.toEpochDay();
    }
}
