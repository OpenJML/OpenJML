// The 'invariants' clause at a call site (#651): an item naming a callee parameter is bound to
// the call's argument, not to a caller field, parameter or local of the same name. Each pair has
// an OK case (verifies only if the binding is right) and a FAILS case (would verify if the item
// were read in the caller's scope).

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

    //@ public normal_behavior
    //@ pure
    public D() { c = new C(); }
}

//@ non_null_by_default
public class T {
    public D q;   // same name as callee's parameter
    public D d;

    //@ public normal_behavior
    //@ pure
    public T() { q = new D(); d = new D(); }

    //@ invariants q.c;
    //@ public normal_behavior
    //@   assignable q.c.x;
    public void callee(D q) {
        q.c.x = 1;
    }

    //@ invariants a.c;
    //@ public normal_behavior
    //@   assignable a.c.x;
    public void callee2(D a, D b) {
        a.c.x = 1;
    }

    // OK: r.c is valid; a binding to the field this.q would fail (this.q.c is not known valid)
    //@ invariants r.c;
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void fieldOK(D r) {
        callee(r);
        //@ assert r.c.x > 0;
    }

    // FAILS at the call: only the field q's c is valid, the argument is r
    //@ invariants q.c;
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void fieldBad(D r) {
        callee(r);
    }

    // FAILS at the assert: after the call r.c's invariant is assumed, not this.q.c's
    //@ invariants r.c;
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void fieldAfterBad(D r) {
        callee(r);
        //@ assert q.c.x > 0;
    }

    // OK: the argument r is valid; the caller's own q is not
    //@ invariants r.c;
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void paramOK(D q, D r) {
        callee(r);
        //@ assert r.c.x > 0;
    }

    // FAILS at the call: the caller's own q is valid, the argument is r
    //@ invariants q.c;
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void paramBad(D q, D r) {
        callee(r);
    }

    // OK: the argument r is valid; the local q is not
    //@ invariants r.c;
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void localOK(D r, D s) {
        D q = s;
        callee(r);
        //@ assert r.c.x > 0;
    }

    // FAILS at the call: the local q (= s) is valid, the argument is r
    //@ invariants s.c;
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void localBad(D r, D s) {
        D q = s;
        callee(r);
    }

    // OK: the argument is the expression this.d
    //@ invariants d.c;
    //@ public normal_behavior
    //@   assignable d.c.x;
    public void exprOK() {
        callee(this.d);
        //@ assert d.c.x > 0;
    }

    // FAILS at the call: d.c is valid, the argument is this.q
    //@ invariants d.c;
    //@ public normal_behavior
    //@   assignable q.c.x;
    public void exprBad() {
        callee(this.q);
    }

    // OK: callee2's item a is its first argument, s
    //@ invariants s.c;
    //@ public normal_behavior
    //@   assignable s.c.x;
    public void positionOK(D r, D s) {
        callee2(s, r);
        //@ assert s.c.x > 0;
    }

    // FAILS at the call: s is valid, but callee2's first argument is r
    //@ invariants s.c;
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void positionBad(D r, D s) {
        callee2(r, s);
    }
}

//@ non_null_by_default
class Base {
    //@ public normal_behavior
    //@ pure
    public Base() {}

    //@ invariants a.c;
    //@ public normal_behavior
    //@   assignable a.c.x;
    public void m(D a) {
        a.c.x = 1;
    }
}

// The override renames the parameter; the inherited item a.c must bind to the argument
//@ non_null_by_default
class Derived extends Base {
    //@ public normal_behavior
    //@ pure
    public Derived() {}

    //@ also public normal_behavior
    //@   assignable b.c.x;
    public void m(D b) {
        b.c.x = 2;
    }
}

//@ non_null_by_default
class User {
    //@ public normal_behavior
    //@ pure
    public User() {}

    // OK: the inherited clause is bound to the argument r
    //@ invariants r.c;
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void overrideOK(Derived x, D r) {
        x.m(r);
        //@ assert r.c.x > 0;
    }

    // FAILS at the call: r.c is not known valid
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void overrideBad(Derived x, D r) {
        x.m(r);
    }
}
