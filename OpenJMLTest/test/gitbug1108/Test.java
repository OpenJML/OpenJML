// #1108: a pure constructor writes only the new object's fields, so pure methods
// on objects that existed before the call keep their values.
final class N {
    final int p;
    //@ public normal_behavior
    //@   requires q >= 0;
    //@   ensures getP() == q;
    //@ pure
    public N(int q) { p = q; }

    //@ public normal_behavior
    //@   ensures \result >= 0;
    //@ pure
    public int getP() { return p < 0 ? 0 : p; }

    //@ public normal_behavior
    //@   ensures \result == (getP() == x.getP());
    //@ pure
    public boolean same(N x) { return getP() == x.getP(); }
}

final class W {
    //@ public normal_behavior
    //@   assignable \everything;
    public W() { }
}

public class Test {
    public static void receiver() {
        N a = new N(7);
        //@ assert a.getP() == 7;
        N b = new N(8);
        //@ assert a.getP() == 7;
        //@ assert b.getP() == 8;
    }

    public static void argument() {
        N a = new N(7);
        N c = new N(7);
        //@ assert a.same(c);
        N b = new N(8);
        //@ assert a.same(c);
    }

    public static void notPure() {
        N a = new N(7);
        //@ assert a.getP() == 7;
        W w = new W();
        //@ assert a.getP() == 7; // not provable: W() may assign anything
    }
}
