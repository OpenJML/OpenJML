package p;
// Run as plain Java after --compile: no JML code executes, and the class loads
public class R {
    static int count() { System.out.println("ghost initializer ran"); return 1; } // must not print
    //@ ghost int g = count();
    //@ model pure public static int q(); // no body: made the class file invalid
    int x;
    public void f() {
        //@ ghost int k = count();
        //@ set g = k;
        //@ assert x < 0; // false, but not checked
        x++;
    }
    public static void main(String[] args) {
        R r = new R();
        r.f();
        System.out.println("x = " + r.x);
    }
}
