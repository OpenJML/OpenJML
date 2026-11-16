import java.util.*;

public class TestIllegalFormatFlagsException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        nullArgument();
        System.out.println("DONE");
    }

    public static void construct() {
        String f = "-#";
        IllegalFormatFlagsException e = new IllegalFormatFlagsException(f);
        //@ assert e.getFlags() == f;
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
        IllegalArgumentException ia = e;
    }

    public static void nullArgument() {
        try {
            new IllegalFormatFlagsException(null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
    }
}
