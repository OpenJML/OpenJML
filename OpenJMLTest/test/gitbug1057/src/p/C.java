package p;
// A nullness modifier before the array type of a .jml declaration applies to the element type, whether the class
// has source or only a class file (#1057)
public class C {
    public void f(A x) {
        //@ assume x.f.length > 0;
        //@ assert x.f[0] != null; // fails: elements nullable
    }
    public void g(A x) {
        //@ assume x.g != null && x.g.length > 0;
        //@ assert x.g[0] != null; // verifies: the array is nullable, not its elements
    }
    public void r(A x) {
        //@ assume x.r() != null && x.r().length > 0;
        //@ assert x.r()[0] != null; // fails: elements nullable
    }
}
