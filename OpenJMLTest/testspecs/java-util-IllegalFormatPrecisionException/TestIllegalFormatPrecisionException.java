import java.util.*;

public class TestIllegalFormatPrecisionException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        System.out.println("DONE");
    }

    public static void construct() {
        IllegalFormatPrecisionException e = new IllegalFormatPrecisionException(-3);
        //@ assert e.getPrecision() == -3;
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
    }
}
