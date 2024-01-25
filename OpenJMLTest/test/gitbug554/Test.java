public class Test<B extends Test> {
    
    //@ public normal_behavior
    //@ ensures \result == 10;
    public int m(B b) { // FIXME - When declared as B (instead of Test), the default nonnullness is not recognized
        return b.mm();
    }
    
    //@ public normal_behavior
    //@ ensures \result == 10;
    public int mm() {
        return 10;
    }
}