// Issue #980: a callee's frame item that indexes a model field (assignable s[n]) is compared with the
// caller's frame by index, when the caller's frame also indexes that model field. The test pins which
// calls are allowed: ok, okRange and okWhole verify; bad (index 0 vs k) and badWhole (all of s vs s[k])
// fail their Assignable checks.
public abstract class S {
    //@ public model \seq<Integer> s;

    //@ requires 0 <= n;
    //@ assignable s[n];
    public abstract void set(int n);

    //@ assignable s;
    public abstract void setAll();

    //@ requires 0 <= k;
    //@ assignable s[k];
    public void ok(int k) { set(k); }

    //@ requires 0 <= k;
    //@ assignable s[k];
    public void bad(int k) { set(0); }

    //@ requires 0 <= i <= j;
    //@ assignable s[i..j];
    public void okRange(int i, int j) { set(i); set(j); }

    //@ assignable s;
    public void okWhole() { set(3); }

    //@ requires 0 <= k;
    //@ assignable s[k];
    public void badWhole(int k) { setAll(); }
}
