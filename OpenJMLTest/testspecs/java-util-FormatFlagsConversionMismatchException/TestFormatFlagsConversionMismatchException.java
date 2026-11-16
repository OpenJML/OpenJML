import java.util.*;

public class TestFormatFlagsConversionMismatchException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        nullArgument();
        System.out.println("DONE");
    }

    public static void construct() {
        String f = "#";
        FormatFlagsConversionMismatchException e = new FormatFlagsConversionMismatchException(f, 'd');
        //@ assert e.getFlags() == f;
        //@ assert e.getConversion() == 'd';
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
    }

    public static void nullArgument() {
        try {
            new FormatFlagsConversionMismatchException(null, 'x');
            //@ unreachable;
        } catch (NullPointerException e) {
        }
    }
}
