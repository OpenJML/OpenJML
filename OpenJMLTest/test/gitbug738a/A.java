public class A implements HasComm {

    //@ also
    //@ ensures \result;
    public /*@ pure @*/ boolean comm(HasComm other){
        return true;
    }
}
