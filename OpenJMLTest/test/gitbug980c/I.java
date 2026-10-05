// Issue #980: a failure found while translating an inherited postcondition (here, that 10 / n is
// well-defined) was reported at the postcondition's character offset but in the file of the
// implementing class (S.java), i.e. at an unrelated place. The test pins that it is reported in I.java.
public interface I {
    //@ ensures \result == 10 / n;
    //@ pure
    public int m(int n);
}
