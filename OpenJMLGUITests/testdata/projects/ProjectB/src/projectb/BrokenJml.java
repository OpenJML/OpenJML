package projectb;

/**
 * JML type error in ProjectB.
 * The requires clause compares an int parameter with a String literal,
 * which is a JML type error caught by OpenJML's type-checker.
 */
public class BrokenJml {
    //@ requires x > "hello"; // JML type error: comparing int with String
    public void method(int x) {
        // intentionally empty
    }
}
