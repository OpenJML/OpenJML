import java.time.DateTimeException;

public class TestDateTimeException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        withCause();
        System.out.println("DONE");
    }

    public static void construct() {
        DateTimeException e = new DateTimeException("bad date");
        //@ assert e.getMessage() == "bad date";
        //@ assert e.getCause() == null;
        RuntimeException r = e;
    }

    public static void withCause() {
        ArithmeticException c = new ArithmeticException();
        DateTimeException e = new DateTimeException("overflow", c);
        //@ assert e.getMessage() == "overflow";
        //@ assert e.getCause() == c;
        DateTimeException f = new DateTimeException("x", null);
        //@ assert f.getCause() == null;
    }
}
