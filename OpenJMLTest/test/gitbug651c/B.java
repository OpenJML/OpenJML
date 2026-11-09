// Issue #651: invariants of objects reached through a field of a parameter (or
// through two fields from 'this') are not assumed at method entry.
// ESC assumes the invariants of the receiver, of each field of the receiver (one
// level) and of each parameter, but not of fields of parameters or deeper fields.
// m1 and m2 are controls that verify. m3, m4, m5 and the Holder constructor fail
// only because of #651; the expected file records those failures until it is fixed.
// Self-contained successor to gitbug651 (whose Map invariant no longer exists in Specs).

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
public class B {
    public C c;
    public D d;

    //@ public normal_behavior
    //@ pure
    public B() { c = new C(); d = new D(); }

    //@ public normal_behavior
    //@   requires true;
    public void m1() {
        //@ assert c.x > 0; // OK: field of this
    }

    //@ public normal_behavior
    //@   requires true;
    public void m2(C p) {
        //@ assert p.x > 0; // OK: parameter
    }

    //@ public normal_behavior
    //@   requires true;
    public void m3(D p) {
        //@ assert p.c.x > 0; // FAILS (#651): field of a parameter
    }

    //@ public normal_behavior
    //@   requires true;
    public void m4() {
        //@ assert d.c.x > 0; // FAILS (#651): field of a field of this
    }

    //@ public normal_behavior
    //@   requires true;
    public void m5(D p) {
        C loc = p.c;
        //@ assert loc.x > 0; // FAILS (#651): same as m3, through a local
    }
}

//@ non_null_by_default
class Holder {
    public C held;
    //@ public invariant held.x > 0;

    //@ public normal_behavior
    //@ pure
    public Holder(D p) {
        held = p.c; // FAILS (#651): invariant of p.c unknown, so Holder's invariant is not established
    }
}
