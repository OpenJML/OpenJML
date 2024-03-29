import java.util.ArrayList;

public class ArrList {
    private /*@ spec_public @*/ ArrayList<String> theList;

    //@ public behavior
    //@   reads \everything;
    //@   requires a != null;
    //@   ensures theList.size() == 1;
    //@   ensures theList.contains(a);
    //@ pure
    public ArrList(String a) {
        theList = new ArrayList<String>();
        theList.add(a);
    }
}
