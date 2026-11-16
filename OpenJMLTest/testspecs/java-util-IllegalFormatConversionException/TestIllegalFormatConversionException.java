import java.util.*;

public class TestIllegalFormatConversionException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        nullArgument();
        System.out.println("DONE");
    }

    public static void construct() {
        IllegalFormatConversionException e = new IllegalFormatConversionException('d', String.class);
        //@ assert e.getConversion() == 'd';
        //@ assert e.getArgumentClass() == String.class;
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
    }

    public static void nullArgument() {
        try {
            new IllegalFormatConversionException('x', null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
    }
}
