package p;

public class A {
    protected /*@ spec_public */ int x;
    //@ public invariant x >= 0;

    //@ public normal_behavior
    //@ pure
    public A() { x = 0; }
}
