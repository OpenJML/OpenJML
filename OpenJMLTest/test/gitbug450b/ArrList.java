// This test case is a different case of Git issue #450; has an NPE with -minQuant

import java.util.ArrayList;

public class ArrList {
    public ArrayList<Integer> theList;

    // Use default assignable, else use assignable theList, theList.*;
    //@ ensures theList != null;
    //@ ensures theList.indexOf(a) == 0;
    public ArrList(int a) {
        theList = new ArrayList<Integer>();
        theList.add(a);
    }

}