import java.util.concurrent.atomic.AtomicLong;
public class TestAtomicLong {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        esc();
        System.out.println("DONE");
    }

    public static void esc() {
        AtomicLong a = new AtomicLong();
        //@ assert a.get() == 0;
        AtomicLong b = new AtomicLong(7);
        //@ assert b.get() == 7;
        a.set(3);
        //@ assert a.get() == 3;
    }
}
