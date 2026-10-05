// Issue #969: an invariant that calls a non-pure method of another class, passing 'this'.
// Checking the callee's argument invariants re-enters A's invariants; the recursion guard
// detects it at A's class declaration, so no method is marked helper and the loop never ends
// (StackOverflowError, then MISMATCHED BLOCKS). The test pins that ESC terminates normally.
public class A {
    public B b = new B();
    //@ public invariant b.ok(this);
}
class B {
    public boolean ok(A x) { return x != null; }
}
