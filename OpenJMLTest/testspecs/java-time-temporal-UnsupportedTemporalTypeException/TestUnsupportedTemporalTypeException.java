import java.time.DateTimeException;
import java.time.temporal.UnsupportedTemporalTypeException;

public class TestUnsupportedTemporalTypeException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        withCause();
        System.out.println("DONE");
    }

    public static void construct() {
        UnsupportedTemporalTypeException e = new UnsupportedTemporalTypeException("unsupported");
        //@ assert e.getMessage() == "unsupported";
        //@ assert e.getCause() == null;
        DateTimeException d = e;
    }

    public static void withCause() {
        IllegalStateException c = new IllegalStateException();
        UnsupportedTemporalTypeException e = new UnsupportedTemporalTypeException("u", c);
        //@ assert e.getMessage() == "u";
        //@ assert e.getCause() == c;
    }
}
