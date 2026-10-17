// Issue #1012: an item of --method that matches no method is reported (a misspelling used to check nothing, silently)
public class MethodOption {
    //@ requires i < Integer.MAX_VALUE;
    //@ ensures \result == i + 1;
    public int inc(int i) { return i + 1; }

    //@ ensures \result == i;      // wrong, but not checked: not selected by --method
    public int dec(int i) { return i - 1; }
}
