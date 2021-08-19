public class B implements HasComm {

    //@ also
    //@ ensures !\result;
    public /*@ pure @*/ boolean comm(HasComm other){
        return false;
    }
}
