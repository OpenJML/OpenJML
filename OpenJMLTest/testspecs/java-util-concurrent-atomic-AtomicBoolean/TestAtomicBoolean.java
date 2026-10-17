import java.util.concurrent.atomic.AtomicBoolean;
public class TestAtomicBoolean {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        esc();
        setAndGet();
        compareAndSet();
        string();
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

    public static void setAndGet() {
        AtomicBoolean a = new AtomicBoolean(false);
        a.set(true);
        //@ assert a.get();
        // FIXME - lazySet is not fully modeled: the specs treat it as set(); its weaker
        //         memory-ordering guarantees toward other threads are not modeled
        a.lazySet(false);
        //@ assert !a.get();
        boolean r = a.getAndSet(true);
        //@ assert !r && a.get();
        r = a.getAndSet(true);
        //@ assert r && a.get();
    }

    public static void compareAndSet() {
        AtomicBoolean a = new AtomicBoolean(false);
        boolean r = a.compareAndSet(false, true);
        //@ assert r && a.get();
        r = a.compareAndSet(false, true);
        //@ assert !r && a.get();
    }

    public static void string() {
        AtomicBoolean a = new AtomicBoolean(true);
        // FIXME - toString is not fully modeled: the specs do not say what string it returns
        String s = a.toString();
        //@ assert s != null;
    }
}
