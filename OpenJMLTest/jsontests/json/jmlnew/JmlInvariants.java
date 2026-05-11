// Exercises JmlMethodClauseInvariantsAdapter: invariants method clause.
public class JmlInvariants {
    int x;
    int y;
    Object obj;

    //@ public normal_behavior
    //@   invariants x, y;
    //@   ensures true;
    public void m() {}

    //@ public normal_behavior
    //@   invariants x, obj, y;
    //@   ensures x >= 0;
    public void n(int k) {}
}
