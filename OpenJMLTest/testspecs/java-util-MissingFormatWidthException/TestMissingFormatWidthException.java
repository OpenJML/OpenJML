import java.util.*;

public class TestMissingFormatWidthException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        nullArgument();
        System.out.println("DONE");
    }

    public static void construct() {
        String f = "-#";
        MissingFormatWidthException e = new MissingFormatWidthException(f);
        //@ assert e.getFormatSpecifier() == f;
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
        IllegalArgumentException ia = e;
    }

    public static void nullArgument() {
        try {
            new MissingFormatWidthException(null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
    }
}
