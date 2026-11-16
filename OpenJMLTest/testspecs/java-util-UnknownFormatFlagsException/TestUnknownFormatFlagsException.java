import java.util.*;

public class TestUnknownFormatFlagsException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        nullArgument();
        System.out.println("DONE");
    }

    public static void construct() {
        String f = "-#";
        UnknownFormatFlagsException e = new UnknownFormatFlagsException(f);
        //@ assert e.getFlags() == f;
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
        IllegalArgumentException ia = e;
    }

    public static void nullArgument() {
        try {
            new UnknownFormatFlagsException(null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
    }
}
