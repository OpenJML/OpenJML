public class CallStack {
    
    public void mm() {
        m(-1);
    }
    //@ public normal_behavior 
    //@ requires x(i);
    public void m(int i) {
        
    }
    //@ public normal_behavior 
    //@ requires pos(i);
    //@ ensures \result == i > 10;
    //@ pure
    public boolean x(int i) {
        return i > 10;
    }
    //@ public normal_behavior 
    //@ ensures \result == i > 0;
    //@ pure
    public boolean pos(int i) {
        return i > 0;
    }
}