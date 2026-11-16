import java.util.*;

public class TestUnknownFormatConversionException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        nullArgument();
        System.out.println("DONE");
    }

    public static void construct() {
        String f = "-#";
        UnknownFormatConversionException e = new UnknownFormatConversionException(f);
        //@ assert e.getConversion() == f;
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
        IllegalArgumentException ia = e;
    }

    public static void nullArgument() {
        try {
            new UnknownFormatConversionException(null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
    }
}
