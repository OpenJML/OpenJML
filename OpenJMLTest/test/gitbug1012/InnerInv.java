// Issue #1012: RAC for inner (non-static) classes.
// - a field of the enclosing class, used by its simple name in an inner class, belongs to Outer.this
// - the enclosing class's instance invariants are checked, for methods of an inner class, on Outer.this
// - for a static nested class, only the enclosing class's static invariants apply
public class InnerInv {
    long x = 1;
    //@ invariant 0 <= x;
    static int s = 0;
    //@ static invariant s >= 0;

    class Inner {
        Inner() {}
        void ok() { x = 5; }        // keeps the enclosing invariant
        long get() { return x; }
        void bad() { x = -1; }      // breaks the enclosing invariant: reported on leaving bad()
    }

    static class Nested {
        long x = -7;                // its own field: InnerInv's instance invariant does not apply to it
        Nested() {}
        void m() {}
    }

    class Mid { class Deep { void bad() { x = -2; } } }

    public static void main(String... a) {
        InnerInv o = new InnerInv();
        Inner i = o.new Inner();
        i.ok();
        System.out.println("x = " + i.get());
        new Nested().m();
        System.out.println("nested OK");
        i.bad();
        o.x = 3;
        o.new Mid().new Deep().bad();
        System.out.println("DONE");
    }
}
