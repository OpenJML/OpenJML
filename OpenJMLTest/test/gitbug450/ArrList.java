// This test case corresponds to Git issue #450

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

    //@ assignable \nothing;
    public static void main(String[] args) {
        ArrList al = new ArrList(1);
        System.out.println(al.theList.get(0));
    }
}