// A non-null field declared only in A.jml and not set by the constructor: NullField is reported at the
// .jml declaration, not at the same offset of this file (#1006)
public class A {
    public int k;

    public A() {
        k = 0;
    }
}
