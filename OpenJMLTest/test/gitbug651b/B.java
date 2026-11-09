public class B {
    private int count;  //@ in N;
    //@ public model int N;
    //@ private represents N = count;

    //@ public normal_behavior
    //@   modifies \everything;
    //@   ensures N == \old(N);  // BOGUS! This should not verify, but it does.
    public void bad() {
        count = 120;
    }
}
// Despite the name, unrelated to #651's invariant problem; companion of gitbug651a.
// With 'count' in N, bad() changes N, so the postcondition 'N == \old(N)' must fail
// (the "BOGUS" comment dates from when it wrongly verified).
