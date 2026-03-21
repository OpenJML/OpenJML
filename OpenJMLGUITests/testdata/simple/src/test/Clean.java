package test;

/**
 * Java class with trivially satisfiable JML specs.
 * Used as a baseline ("no errors expected") in GUI tests.
 */
public class Clean {
    //@ requires x >= 0;
    //@ ensures \result >= 0;
    public int identity(int x) {
        return x;
    }
}
