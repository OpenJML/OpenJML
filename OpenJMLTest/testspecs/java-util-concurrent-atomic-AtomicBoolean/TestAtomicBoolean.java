import java.util.concurrent.atomic.AtomicBoolean;
public class TestAtomicBoolean {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        esc();
        System.out.println("DONE");
    }

    public static void esc() {
        AtomicBoolean a = new AtomicBoolean();
        //@ assert !a.get();
        AtomicBoolean b = new AtomicBoolean(true);
        //@ assert b.get();
        boolean r = b.compareAndSet(true, false); // needs value == 1, not just get()
        //@ assert r;
    }
}
