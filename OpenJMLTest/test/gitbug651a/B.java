public class B {
    private int count; // Should get an error that count is not in N, even though N depends on count
    //@ public model int N;
    //@ private represents N = count;

    //@ public normal_behavior
    //@   modifies \everything;
    //@   ensures N == \old(N);  // BOGUS! This should not verify, but it does.
    public void bad() {
        count = 120;
    }
}
// Despite the name, unrelated to #651's invariant problem (this file first held the
// '\invariant_for' workaround for #651; it was repurposed in 59babcbd6b, 2020).
// Tests that a represents clause for model field N may read 'count' only if 'count'
// is 'in N': the expected result is that type error. gitbug651b is the corrected
// version and must report the postcondition failure in bad().
