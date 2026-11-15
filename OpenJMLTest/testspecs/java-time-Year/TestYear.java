import java.time.DateTimeException;
import java.time.Year;

public class TestYear {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        leap();
        construct();
        arithmetic();
        comparison();
        limits();
        System.out.println("DONE");
    }

    public static void leap() {
        //@ assert Year.isLeap(2024) && !Year.isLeap(2023);
        //@ assert !Year.isLeap(1900) && Year.isLeap(2000);
        //@ assert Year.isLeap(-4) && !Year.isLeap(-1);
    }

    public static void construct() {
        Year y = Year.of(2024);
        //@ assert y.getValue() == 2024 && y.isLeap() && y.length() == 366;
        Year z = Year.of(2100);
        //@ assert !z.isLeap() && z.length() == 365;
    }

    public static void arithmetic() {
        Year y = Year.of(2000);
        Year z = y.plusYears(24);
        //@ assert z.getValue() == 2024;
        Year w = y.minusYears(2001);
        //@ assert w.getValue() == -1;
    }

    public static void comparison() {
        Year a = Year.of(1999);
        Year b = Year.of(2000);
        //@ assert a.compareTo(b) == -1 && a.isBefore(b) && b.isAfter(a);
        //@ assert a.equals(Year.of(1999)) && !a.equals(b) && a.hashCode() == 1999;
    }

    public static void limits() {
        try {
            Year.of(Year.MAX_VALUE + 1);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
        Year y = Year.of(Year.MAX_VALUE);
        try {
            y.plusYears(1);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
        try {
            y.minusYears(Long.MIN_VALUE);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
    }
}
