public class A {
    boolean b;
    
    //@ ensures b == \\old(b); // Intentional error
    void m() {}
}