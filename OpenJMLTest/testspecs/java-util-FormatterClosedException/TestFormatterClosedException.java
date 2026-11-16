import java.util.*;

public class TestFormatterClosedException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        System.out.println("DONE");
    }

    public static void construct() {
        FormatterClosedException e = new FormatterClosedException();
        //@ assert e.getMessage() == null;
        //@ assert e.getCause() == null;
        IllegalStateException is = e;
    }
}
