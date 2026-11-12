// #1105: the invariants of an object a field refers to are assumed at method entry, so they must
// hold again at exit (normal and exceptional), and a constructor must establish them.
// Each method's comment says whether it should verify or fail.

//@ non_null_by_default
class C {
    public int x;
    //@ public invariant x > 0;

    //@ public normal_behavior
    //@   ensures x == 1;
    //@ pure
    public C() { x = 1; }
}

//@ non_null_by_default
public class T {
    public C f;
    public /*@ nullable */ C g;
    public static C s = new C();

    // OK: f's invariant holds at the end
    //@ public normal_behavior
    public T() { f = new C(); f.x = 2; g = null; }

    // FAILS: the constructor leaves f's invariant broken
    //@ public normal_behavior
    public T(int k) { f = new C(); f.x = 0; g = null; }

    // FAILS: breaks f's invariant and returns normally
    //@ public normal_behavior
    //@   assignable f.x;
    public void breakNormal() { f.x = 0; }

    // FAILS: breaks f's invariant and throws
    //@ public exceptional_behavior
    //@   assignable f.x;
    //@   signals_only RuntimeException;
    public void breakExc() { f.x = 0; throw new RuntimeException(); }

    // OK: restores the invariant before returning
    //@ public normal_behavior
    //@   assignable f.x;
    public void restore() { f.x = 0; f.x = 3; }

    // OK: the nullable field is checked only when non-null
    //@ public normal_behavior
    //@   assignable g;
    public void nullableField() { g = null; }

    // FAILS: breaks the invariant of the object in the nullable field
    //@ public normal_behavior
    //@   requires g != null && g != f;
    //@   assignable g.x;
    public void breakNullable() { g.x = 0; }

    // OK: for a static field only its type's static invariants are assumed at entry and checked at
    // exit, as at entry (C has none), so breaking the object's instance invariant is not reported
    //@ public normal_behavior
    //@   assignable s.x;
    public static void staticField() { s.x = 0; }

    // OK: pure methods are not rechecked
    //@ public normal_behavior
    //@ pure
    public int get() { return f.x; }
}
