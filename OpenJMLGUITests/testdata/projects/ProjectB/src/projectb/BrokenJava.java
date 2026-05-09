package projectb;

/**
 * Java compile error in ProjectB.
 * ProjectB has JML nature — both Java and JML errors should appear.
 */
public class BrokenJava {
    public void method() {
        int x = alsoUndefined; // Java error: cannot find symbol
    }
}
