// An enum with both a .java and a .jml: the implicit enum axioms must be entered once (#1099)
public enum E {
    A, B;

    public int v() {
        return ordinal() + 1;
    }

    public static void m() {
        //@ assert A != B;
        //@ assert B.ordinal() == 1;
        //@ assert B.v() == 2;
    }
}
