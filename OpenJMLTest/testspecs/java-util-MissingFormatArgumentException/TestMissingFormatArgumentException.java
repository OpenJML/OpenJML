import java.util.*;

public class TestMissingFormatArgumentException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        nullArgument();
        System.out.println("DONE");
    }

    public static void construct() {
        String f = "-#";
        MissingFormatArgumentException e = new MissingFormatArgumentException(f);
        //@ assert e.getFormatSpecifier() == f;
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
        IllegalArgumentException ia = e;
    }

    public static void nullArgument() {
        try {
            new MissingFormatArgumentException(null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
    }
}
