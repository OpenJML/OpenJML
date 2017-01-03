import java.util.ArrayList;

public class ArrList {
    private /*@ spec_public @*/ ArrayList<String> theList;

    //@ public normal_behavior
    //@   assignable theList, theList.objectState; accessible \everything;
    //@   requires a != null;
    //@   ensures theList != null;
    //@   ensures theList.size() == 1;
    //@   ensures theList.contains(a);
    public ArrList(String a) {
        theList = new ArrayList<String>();
        theList.add(a);
    }
}