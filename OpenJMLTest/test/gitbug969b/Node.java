// Issue #969: an invariant that calls a non-pure method of its own class with an argument of
// that class. The recursion is detected at the argument 'next', so no method is marked helper
// and the loop never ends (StackOverflowError / MISMATCHED BLOCKS). Without the argument
// (e.g. 'next.get() != null') ESC terminates. The test pins that ESC terminates normally.
// Everything is nullable so that no nullness failures obscure the output.
public class Node {
    public /*@ nullable */ Node next;
    //@ public invariant self(next) == next;
    public /*@ nullable */ Node self(/*@ nullable */ Node s) { return s; }
}
