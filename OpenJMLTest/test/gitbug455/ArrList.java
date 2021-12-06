import java.util.ArrayList;

public class ArrList {
    private /*@ spec_public @*/ ArrayList<Integer> theList;

    //@ public behavior
    //@   reads \everything;
    //@   requires a != null;
    //@   ensures theList.size() == 1;
    //@   ensures theList.contains(a);
    //@ pure
    public ArrList(Integer a) {
        theList = new ArrayList<Integer>();
        theList.add(a);
    }
}
