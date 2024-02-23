//@ nullable_by_default
class C<T> {
}

//@ nullable_by_default
class B {

    public /*@ nullable */ C<Integer> xyz;

    //@ public normal_behavior
    //@   ensures true;
    public C<Integer> getXyz() {
        return null;
    }
}
//@ non_null_by_default
public final class Test {
    
    //@ public normal_behavior
    //@   ensures true;
    public void TestMethod(B b) {  // fails feasibility check #1 (end of preconditions), but should be OK
        b.getXyz();
    }
}

// This failure requires TestMethod to have the B parameter and the xyz field call getXyz to have a result type with type argument
// openjml --esc --check-feasibility=precondition --dir ../test/gitbug654