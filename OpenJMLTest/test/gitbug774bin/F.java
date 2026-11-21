import p.B;
public class F {
    public void m1(B b) { //@ assert B.LIT == 5 && B.EXPR == 5 && b.IL == 7;
    }
    public void m2() { //@ assert B.NONCONST == 99;
    }
    public void m3(B b) { //@ assert b.IFINALNC == 99;
    }
    public void m4() { //@ assert B.NONFINAL == 99;
    }
}
