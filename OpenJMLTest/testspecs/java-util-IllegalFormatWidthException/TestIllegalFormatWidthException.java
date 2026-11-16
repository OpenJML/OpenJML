import java.util.*;

public class TestIllegalFormatWidthException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        System.out.println("DONE");
    }

    public static void construct() {
        IllegalFormatWidthException e = new IllegalFormatWidthException(7);
        //@ assert e.getWidth() == 7;
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
    }
}
