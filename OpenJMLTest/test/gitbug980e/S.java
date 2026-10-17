// Issue #980: in a frame clause, x[i] is a location only if x is an array or a model field; a model
// field's index must be an integer (it is applied to the arrays mapped into the model field).
// The test pins the two type errors: g[n] (g is a ghost \seq, not a model field) and m["a"].
public abstract class S {
    //@ public ghost \seq<Integer> g;
    //@ public model \map<String,Integer> m;
    //@ public model \seq<Integer> s;

    //@ assignable g[n];
    public abstract void a(int n);

    //@ assignable m["a"];
    public abstract void b();

    //@ assignable s[n];
    public abstract void ok(int n);
}
