import java.util.*;

public class TestIllegalFormatCodePointException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        System.out.println("DONE");
    }

    public static void construct() {
        IllegalFormatCodePointException e = new IllegalFormatCodePointException(0x110000);
        //@ assert e.getCodePoint() == 0x110000;
        //@ assert e.getCause() == null;
        String m = e.getMessage();
        //@ assert m != null;
        IllegalFormatException s = e;
    }
}
