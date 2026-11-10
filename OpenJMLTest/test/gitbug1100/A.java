// Issue #1100: a model method with a body and parameters, declared in the .jml of a class
// compiled from source, crashed javac's Flow analysis when the class declaration in this
// file starts later than the model method's position in the .jml

public class A {
    public int m() {
        return 1;
    }
}
