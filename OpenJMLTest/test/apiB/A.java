public class A {
    
    public void m() {}
    
    //@ ensures \result == 43;
    public int n() {
        return 42;
    }
}