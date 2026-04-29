package projecta;

/**
 * Java class with a compile error (undefined symbol).
 * ProjectA has NO JML nature — used to verify that JML checking
 * is not applied to projects without the nature.
 *
 * The class also carries JML annotations so that if it *were*
 * checked for JML, an error would be visible.
 */
public class Broken {
    //@ ensures \result >= 0;
    public int getValue() {
        return undefinedSymbol; // Java compile error: cannot find symbol
    }
}
