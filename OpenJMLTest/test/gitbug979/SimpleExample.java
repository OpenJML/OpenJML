// gitbug979: an 'in' clause after a declaration of several fields applies to all of them
public class SimpleExample {
    //@ public model int f;
    private int _f, x; //@ in f;
    //@ private represents f = _f;

    //@ assignable f;
    public void setBoth(int v) {
        _f = v; // both _f and x are in f
        x = v;
    }
}
