import java.util.*;

public class TestIllformedLocaleException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        System.out.println("DONE");
    }

    public static void construct() {
        IllformedLocaleException e1 = new IllformedLocaleException("bad", 3);
        //@ assert e1.getErrorIndex() == 3;
        //@ assert e1.getCause() == null;
        IllformedLocaleException e2 = new IllformedLocaleException("bad");
        //@ assert e2.getErrorIndex() == -1;
        //@ assert e2.getMessage() == "bad";
        //@ assert e2.getCause() == null;
        IllformedLocaleException e3 = new IllformedLocaleException();
        //@ assert e3.getErrorIndex() == -1;
        //@ assert e3.getMessage() == null;
        RuntimeException r = e3;
    }
}
