// The 'invariants' clause (#651) with several specification cases: the clause belongs to the
// method, not to a case, so its items are assumed at entry under any case, asserted at every
// exit, and checked at a call whichever callee case applies. At exit, a parameter named in the
// clause denotes its pre-state value (as in ensures), even if the body reassigns it.

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

    // OK: p.c's invariant is assumed under either case
    //@ invariants p.c;
    //@ public normal_behavior
    //@   requires b;
    //@   assignable \nothing;
    //@ also public exceptional_behavior
    //@   requires !b;
    //@   assignable \nothing;
    //@   signals_only RuntimeException;
    public void entryBoth(D p, boolean b) {
        //@ assert p.c.x > 0;
        if (!b) throw new RuntimeException();
    }

    // FAILS at the clause item, on the exceptional exit only (second case)
    //@ invariants p.c;
    //@ public normal_behavior
    //@   requires b;
    //@   assignable p.c.x;
    //@ also public exceptional_behavior
    //@   requires !b;
    //@   assignable p.c.x;
    //@   signals_only RuntimeException;
    public void exitExceptionalCase(D p, boolean b) {
        if (!b) { p.c.x = 0; throw new RuntimeException(); }
        p.c.x = 2;
    }

    // FAILS at the clause item, on the normal exit only (first case)
    //@ invariants p.c;
    //@ public normal_behavior
    //@   requires b;
    //@   assignable p.c.x;
    //@ also public exceptional_behavior
    //@   requires !b;
    //@   assignable p.c.x;
    //@   signals_only RuntimeException;
    public void exitNormalCase(D p, boolean b) {
        if (!b) { p.c.x = 2; throw new RuntimeException(); }
        p.c.x = 0;
    }

    // Callee with two disjoint cases
    //@ invariants q.c;
    //@ public normal_behavior
    //@   requires k > 0;
    //@   assignable q.c.x;
    //@ also public normal_behavior
    //@   requires k <= 0;
    //@   assignable \nothing;
    public void callee(D q, int k) {
        if (k > 0) q.c.x = k;
    }

    // OK: only the second callee case applies; its entry check still holds and its exit is assumed
    //@ invariants r.c;
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void callerOK(D r) {
        callee(r, 0);
        //@ assert r.c.x > 0;
    }

    // FAILS at the call: only the second callee case applies, but the clause is still checked
    //@ public normal_behavior
    //@   assignable r.c.x;
    public void callerBad(D r) {
        callee(r, 0);
    }

    // OK: the exit check is on the original p (pre-state), whose c is untouched, not on 'other'
    //@ invariants p.c;
    //@ public normal_behavior
    //@   assignable \nothing;
    public void reassignOK(D p, D other) {
        p = other;
    }

    // FAILS at the clause item: breaks the original p.c, then reassigns p to a valid object
    //@ invariants p.c;
    //@ public normal_behavior
    //@   assignable p.c.x;
    public void reassignBad(D p) {
        p.c.x = 0;
        p = new D();
    }
}
