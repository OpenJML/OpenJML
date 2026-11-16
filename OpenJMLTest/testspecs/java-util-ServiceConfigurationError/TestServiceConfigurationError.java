import java.util.*;

public class TestServiceConfigurationError {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        System.out.println("DONE");
    }

    public static void construct() {
        ServiceConfigurationError e1 = new ServiceConfigurationError("s");
        //@ assert e1.getMessage() == "s";
        //@ assert e1.getCause() == null;
        RuntimeException r = new RuntimeException();
        ServiceConfigurationError e2 = new ServiceConfigurationError("t", r);
        //@ assert e2.getMessage() == "t";
        //@ assert e2.getCause() == r;
        Error er = e2;
    }
}
