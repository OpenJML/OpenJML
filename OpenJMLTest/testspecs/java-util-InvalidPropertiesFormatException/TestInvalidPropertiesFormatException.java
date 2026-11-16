import java.util.*;

public class TestInvalidPropertiesFormatException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        System.out.println("DONE");
    }

    public static void construct() {
        InvalidPropertiesFormatException e1 = new InvalidPropertiesFormatException("p");
        //@ assert e1.getMessage() == "p";
        //@ assert e1.getCause() == null;
        RuntimeException r = new RuntimeException();
        InvalidPropertiesFormatException e2 = new InvalidPropertiesFormatException(r);
        //@ assert e2.getCause() == r;
        java.io.IOException io = e2;
    }
}
