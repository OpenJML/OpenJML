package p;
//@ non_null_by_default
public class A {
    public /*@ nullable */ Object f0 = null;
    public /*@ nullable */ Object[] f1 = new Object[1];
    public Object /*@ nullable */ [] f2 = null;
    public /*@ nullable */ Object /*@ nullable */ [] f3 = null;
    //@ ensures p != null;
    public void m0(/*@ nullable */ Object p) {}
    //@ requires p.length > 0;
    //@ ensures p[0] != null;
    public void m1(/*@ nullable */ Object[] p) {}
    //@ ensures p != null;
    public void m2(Object /*@ nullable */ [] p) {}
    //@ spec_pure
    public /*@ nullable */ Object r0() { return null; }
    //@ spec_pure
    public /*@ nullable */ Object[] r1() { return new Object[1]; }
    //@ spec_pure
    public Object /*@ nullable */ [] r2() { return null; }
    //@ spec_pure
    public /*@ nullable */ Object /*@ non_null */ [] r3() { return new Object[1]; }
}
