import java.util.concurrent.atomic.AtomicInteger;
public class TestAtomicInteger {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        esc();
        lazySet();
        compareAndSet();
        getAndModify();
        modifyAndGet();
        update();
        conversions();
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

    public static void lazySet() {
        AtomicInteger a = new AtomicInteger(7);
        // FIXME - lazySet is not fully modeled: the specs treat it as set(); its weaker
        //         memory-ordering guarantees toward other threads are not modeled
        a.lazySet(3);
        //@ assert a.get() == 3;
    }

    public static void compareAndSet() {
        AtomicInteger a = new AtomicInteger(5);
        boolean r = a.compareAndSet(5, 6);
        //@ assert r && a.get() == 6;
        r = a.compareAndSet(5, 7);
        //@ assert !r && a.get() == 6;
    }

    public static void getAndModify() {
        AtomicInteger a = new AtomicInteger(5);
        int r = a.getAndIncrement();
        //@ assert r == 5 && a.get() == 6;
        r = a.getAndDecrement();
        //@ assert r == 6 && a.get() == 5;
        r = a.getAndAdd(10);
        //@ assert r == 5 && a.get() == 15;
        r = a.getAndSet(3);
        //@ assert r == 15 && a.get() == 3;
    }

    public static void modifyAndGet() {
        AtomicInteger a = new AtomicInteger(5);
        int r = a.incrementAndGet();
        //@ assert r == 6 && a.get() == 6;
        r = a.decrementAndGet();
        //@ assert r == 5 && a.get() == 5;
        r = a.addAndGet(10);
        //@ assert r == 15 && a.get() == 15;
    }

    public static void update() {
        AtomicInteger a = new AtomicInteger(5);
        int old = a.get();
        int r = a.getAndUpdate(x -> x + 1);
        //@ assert r == old;
        r = a.updateAndGet(x -> x + 1);
        //@ assert r == a.get();
        old = a.get();
        r = a.getAndAccumulate(3, (x, y) -> x + y);
        //@ assert r == old;
        r = a.accumulateAndGet(3, (x, y) -> x + y);
        //@ assert r == a.get();
    }

    public static void conversions() {
        AtomicInteger a = new AtomicInteger(7);
        int i = a.intValue();
        //@ assert i == 7;
        long n = a.longValue();
        //@ assert n == 7L;
        // FIXME - float: float f = a.floatValue(); //@ assert f == 7.0f;
        // FIXME - double: double d = a.doubleValue(); //@ assert d == 7.0;
        // FIXME - toString is not fully modeled: the specs do not say what string it returns
        String s = a.toString();
        //@ assert s != null;
    }
}
