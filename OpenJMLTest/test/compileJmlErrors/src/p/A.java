package p;
// --compile type-checks JML (this is what distinguishes it from -no-jml)
public class A {
    int x;
    //@ ghost int g;
    //@ invariant y > 0; // error: y is not declared
    public void f() {
        //@ set g = true; // error: boolean to int
    }
}
