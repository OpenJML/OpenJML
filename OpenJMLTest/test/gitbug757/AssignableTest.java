
public class AssignableTest {
    //@ public invariant store.length == 1;

    //@ spec_public
    private final int[] store = new int[1]; //@ maps store[*] \into objectState;

    //@ assignable objectState;
    public void set(int value) {
        store[0] = value;
    }
}