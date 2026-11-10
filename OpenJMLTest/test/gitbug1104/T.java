// #1104: the invariants of a reference-typed parameter must hold on normal as well as exceptional
// exit, for the argument passed in (its pre-state value), even if the body reassigns the parameter.

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
    //@ public normal_behavior
    //@   assignable c.x;
    public void breakNormal(C c) { c.x = 0; }                 // FAILS

    //@ public normal_behavior
    //@   assignable c.x;
    public void keep(C c) { c.x = 5; }                        // OK

    //@ public normal_behavior
    //@   assignable c.x;
    public void reassignBad(C c) { c.x = 0; c = new C(); }    // FAILS: the original c is broken

    //@ public normal_behavior
    //@   assignable \nothing;
    public void reassignOK(C c, C d) { c = d; }               // OK

    //@ public exceptional_behavior
    //@   assignable c.x;
    //@   signals_only RuntimeException;
    public void breakExc(C c) { c.x = 0; throw new RuntimeException(); }  // FAILS

    //@ public normal_behavior
    //@   assignable c.x;
    public void caller(C c) { keep(c); }                      // OK
}
