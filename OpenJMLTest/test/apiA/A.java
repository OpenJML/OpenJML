public class A {
    
    public void m() {}
    
    //@ ensures \result == 42;
    public int n() {
        return 42;
    }
}
