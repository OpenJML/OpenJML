// This test case is a different case of Git issue #450; has an NPE with -minQuant

import java.util.ArrayList;

public class ArrList {
    public ArrayList<Integer> theList;

    // Use default assignable, else use assignable theList, theList.*;
    //@ ensures theList != null;
    // @ ensures theList.indexOf(a) == 0;
    public ArrList(int a) {
        theList = new ArrayList<Integer>();
        theList.add(a);
        //@ assert theList.size() == 1;
        //@ assert theList.values.length == 1;
        //@ assert theList.values[0].theInteger == a;
        //@ assert theList.values[0] == a;
        //@ assert theList.values[0].uniqueHash == a;
        //@ assert theList.values[0].uniqueHash == ((Integer)a).uniqueHash;
        //@ assert (\exists int i; (0 <= i < theList.size()) ==> theList.values[i] == a);
        //@ assert (\forall int i; (0 <= i < theList.size()) ==> theList.values[i] == a);
        //@ assert (\exists int i; (0 <= i < theList.size()) ==> java.util.Collection.nullequals(theList.values[i], (Integer)a));
        //@ assert (\forall int i; (0 <= i < theList.size()) ==> java.util.Collection.nullequals(theList.values[i], (Integer)a));
        int k = theList.indexOf(a);
        //@ show k;
        // @ assert k == 0;
    }
    
    public void m(Integer a) {
        theList = new ArrayList<Integer>();
        theList.add(a);
        //@ assert theList.size() == 1;
        //@ assert theList.values.length == 1;
        //@ assert theList.values[0] == a;
        //@ assert java.util.Collection.nullequals(a,theList.values[0]);
        //@ assert (\exists int i; (0 <= i < theList.size()) ==> theList.values[i] == a);
        //@ assert (\forall int i; (0 <= i < theList.size()) ==> theList.values[i] == a);
        //@ assert (\exists int i; (0 <= i < theList.size()) ==> theList.values[i].uniqueHash == a.uniqueHash);
        //@ assert (\forall int i; (0 <= i < theList.size()) ==> theList.values[i].uniqueHash == a.uniqueHash);
        //@ assert (\exists int i; (0 <= i < theList.size()) ==> java.util.Collection.nullequals(a, theList.values[i]));
        //@ assert (\forall int i; (0 <= i < theList.size()) ==> java.util.Collection.nullequals(a, theList.values[i]));
        int k = theList.indexOf(a);
        //@ show k;
        //@ assert k == 0;
    }
    
}