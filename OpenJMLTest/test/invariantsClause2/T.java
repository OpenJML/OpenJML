// The 'invariants' method-spec clause (#651): it lists object values whose invariants are
// added to the default set (receiver, its fields, parameters): assumed at method entry,
// asserted at normal and exceptional exit, asserted by a caller before a call and assumed
// after it. Each method's comment says whether it should verify or fail, and why.

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
class D {
    public C c;
    public /*@ nullable */ C nc;

    //@ public normal_behavior
    //@ pure
    public D() { c = new C(); nc = null; }
}

//@ non_null_by_default
public class T {
    public D d;

    //@ public normal_behavior
    //@ pure
    public T() { d = new D(); }

    // OK: p.c's invariant comes from the clause
    //@ invariants p.c;
    //@ public normal_behavior
    //@   requires true;
    public void entryParamField(D p) {
        //@ assert p.c.x > 0;
    }

    // OK: d.c (two fields from this) comes from the clause
    //@ invariants d.c;
    //@ public normal_behavior
    //@   requires true;
    public void entryFieldField() {
        //@ assert d.c.x > 0;
    }

    // OK: a nullable item is only constrained when it is not null
    //@ invariants p.nc;
    //@ public normal_behavior
    //@   requires true;
    public void entryNullable(D p) {
        //@ assert p.nc != null ==> p.nc.x > 0;
    }

    // FAILS: invariant of p.c is broken at normal exit
    //@ invariants p.c;
    //@ public normal_behavior
    //@   assignable p.c.x;
    public void exitNormal(D p) {
        p.c.x = 0;
    }

    // FAILS: invariant of p.c is broken at exceptional exit
    //@ invariants p.c;
    //@ public exceptional_behavior
    //@   assignable p.c.x;
    //@   signals_only RuntimeException;
    public void exitExceptional(D p) {
        p.c.x = 0;
        throw new RuntimeException();
    }

    // OK: the exit check is on the post-state value of p.c, a new valid object
    //@ invariants p.c;
    //@ public normal_behavior
    //@   assignable p.c;
    public void exitPostState(D p) {
        p.c = new C();
    }

    // Callee for the call-site tests: requires p.c valid; restores it on exit
    //@ invariants p.c;
    //@ public normal_behavior
    //@   assignable p.c.x;
    public void callee(D p) {
        p.c.x = 1;
    }

    // OK: caller has p.c's invariant (its own clause), so the callee's entry check holds,
    // and after the call the callee's exit guarantee is assumed
    //@ invariants p.c;
    //@ public normal_behavior
    //@   assignable p.c.x;
    public void callerOK(D p) {
        callee(p);
        //@ assert p.c.x > 0;
    }

    // FAILS: caller does not know p.c's invariant, so the call's entry check fails
    //@ public normal_behavior
    //@   assignable p.c.x;
    public void callerBad(D p) {
        callee(p);
    }
}

//@ non_null_by_default
class Holder {
    public C held;
    //@ public invariant held.x > 0;

    // OK: constructor assumes the clause's invariants (with parameter and static ones)
    //@ invariants p.c;
    //@ public normal_behavior
    //@ pure
    public Holder(D p) {
        held = p.c;
    }

    // FAILS: a constructor does not assume its own instance invariants on entry, but asserts them on exit
    //@ public normal_behavior
    //@ pure
    public Holder(C q, int k) {
        held = q;
        held.x = k;
    }
}

//@ non_null_by_default
class Base {
    // The clause is inherited by overrides
    //@ invariants p.c;
    //@ public normal_behavior
    //@   requires true;
    public void m(D p) {}
}

//@ non_null_by_default
class Derived extends Base {
    // OK: p.c's invariant comes from the clause on Base.m
    //@ also public normal_behavior
    //@   requires true;
    @Override
    public void m(D p) {
        //@ assert p.c.x > 0;
    }
}
