import java.util.concurrent.atomic.AtomicInteger;
public class TestAtomicInteger {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        esc();
        System.out.println("DONE");
    }

    public static void esc() {
        AtomicInteger a = new AtomicInteger();
        //@ assert a.get() == 0;
        AtomicInteger b = new AtomicInteger(7);
        //@ assert b.get() == 7;
        a.set(3);
        //@ assert a.get() == 3;
    }
}
