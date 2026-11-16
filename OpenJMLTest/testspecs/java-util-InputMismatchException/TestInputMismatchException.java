import java.util.*;

public class TestInputMismatchException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        System.out.println("DONE");
    }

    public static void construct() {
        InputMismatchException e1 = new InputMismatchException("x");
        //@ assert e1.getMessage() == "x";
        //@ assert e1.getCause() == null;
        InputMismatchException e2 = new InputMismatchException();
        //@ assert e2.getMessage() == null;
        NoSuchElementException ns = e2;
    }
}
