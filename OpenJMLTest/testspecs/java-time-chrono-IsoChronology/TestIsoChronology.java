import java.time.chrono.IsoChronology;

public class TestIsoChronology {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        leap();
        System.out.println("DONE");
    }

    public static void leap() {
        IsoChronology c = IsoChronology.INSTANCE;
        //@ assert c.isLeapYear(2024) && !c.isLeapYear(2023);
        //@ assert !c.isLeapYear(1900) && c.isLeapYear(2000);
        //@ assert c.isLeapYear(-4) && !c.isLeapYear(-1);
    }
}
