import java.time.*;

public class TestLocalDate {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        constants();
        construct();
        dayOfYear();
        lengths();
        withers();
        years();
        months();
        days();
        epochDays();
        comparison();
        exceptions();
        System.out.println("DONE");
    }

    public static void constants() {
        //@ check LocalDate.EPOCH.getYear() == 1970 && LocalDate.EPOCH.getMonthValue() == 1 && LocalDate.EPOCH.toEpochDay() == 0;
        //@ check LocalDate.MAX.getDayOfMonth() == 31;
    }

    public static void construct() {
        LocalDate a = LocalDate.of(2024, 2, 29);
        //@ check a.getYear() == 2024 && a.getMonthValue() == 2 && a.getDayOfMonth() == 29;
        //@ check a.getMonth() == Month.FEBRUARY && a.isLeapYear();
    }

    public static void dayOfYear() {
        LocalDate b = LocalDate.of(2023, Month.DECEMBER, 31);
        //@ check b.getMonthValue() == 12 && b.getDayOfYear() == 365;
    }

    public static void lengths() {
        LocalDate a = LocalDate.of(2023, 2, 1);
        //@ check a.lengthOfMonth() == 28 && a.lengthOfYear() == 365 && !a.isLeapYear();
        LocalDate b = LocalDate.of(2000, 4, 10);
        //@ check b.lengthOfMonth() == 30 && b.lengthOfYear() == 366;
    }

    public static void withers() {
        LocalDate a = LocalDate.of(2024, 3, 31);
        LocalDate b = a.withMonth(4);
        //@ check b.getMonthValue() == 4 && b.getDayOfMonth() == 30;
        LocalDate c = LocalDate.of(2024, 2, 29).withYear(2023);
        //@ check c.getMonthValue() == 2 && c.getDayOfMonth() == 28;
        LocalDate d = a.withDayOfMonth(1);
        //@ check d.getYear() == 2024 && d.getMonthValue() == 3 && d.getDayOfMonth() == 1;
    }

    public static void years() {
        LocalDate a = LocalDate.of(2024, 2, 29);
        LocalDate b = a.plusYears(4);
        //@ check b.getYear() == 2028 && b.getDayOfMonth() == 29;
        LocalDate c = a.minusYears(1);
        //@ check c.getYear() == 2023 && c.getMonthValue() == 2 && c.getDayOfMonth() == 28;
    }

    public static void months() {
        LocalDate a = LocalDate.of(2024, 1, 31);
        LocalDate b = a.plusMonths(1);
        //@ check b.getYear() == 2024 && b.getMonthValue() == 2 && b.getDayOfMonth() == 29;
        LocalDate c = a.minusMonths(13);
        //@ check c.getYear() == 2022 && c.getMonthValue() == 12 && c.getDayOfMonth() == 31;
        LocalDate d = a.plusMonths(11);
        //@ check d.getYear() == 2024 && d.getMonthValue() == 12;
    }

    public static void days() {
        LocalDate a = LocalDate.of(2024, 5, 10);
        LocalDate b = a.plusDays(15);
        //@ check b.getYear() == 2024 && b.getMonthValue() == 5 && b.getDayOfMonth() == 25;
        LocalDate c = a.minusDays(9);
        //@ check c.getDayOfMonth() == 1 && c.getMonthValue() == 5;
        LocalDate d = a.plusDays(30);
        //@ check d.toEpochDay() == a.toEpochDay() + 30;
        LocalDate e = a.plusWeeks(2);
        //@ check e.toEpochDay() == a.toEpochDay() + 14;
    }

    public static void epochDays() {
        LocalDate a = LocalDate.ofEpochDay(0);
        //@ check a.toEpochDay() == 0;
        LocalDate b = LocalDate.ofEpochDay(4);
        //@ check b.getDayOfWeek() == DayOfWeek.MONDAY; // 1970-01-05
        //@ check LocalDate.EPOCH.getDayOfWeek() == DayOfWeek.THURSDAY;
    }

    public static void comparison() {
        LocalDate a = LocalDate.of(2024, 5, 10);
        LocalDate b = LocalDate.of(2024, 6, 1);
        boolean bb = a.compareTo(b) < 0 && a.isBefore(b) && !a.isAfter(b) && !a.isEqual(b);
        //@ check bb;
        bb = a.equals(LocalDate.of(2024, 5, 10)) && !a.equals(b) && !a.equals("2024-05-10");
        //@ check bb;
    }

    public static void exceptions() {
        try {
            LocalDate.of(2023, 2, 29);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
        try {
            LocalDate.of(2024, 13, 1);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
        try {
            LocalDate.MAX.plusDays(1);
            //@ unreachable;
        } catch (DateTimeException | ArithmeticException e) {
        }
        try {
            LocalDate.of(2024, 4, 30).withDayOfMonth(31);
            //@ unreachable;
        } catch (DateTimeException e) {
        }
    }
}
