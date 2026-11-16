import java.util.*;

public class TestDuplicateFormatFlagsException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        nullArgument();
        System.out.println("DONE");
    }

    public static void construct() {
        String f = "-#";
        DuplicateFormatFlagsException e = new DuplicateFormatFlagsException(f);
        //@ assert e.getFlags() == f;
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
        IllegalArgumentException ia = e;
    }

    public static void nullArgument() {
        try {
            new DuplicateFormatFlagsException(null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
    }
}
