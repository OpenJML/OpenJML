public class B implements HasComm {

    //@ also
	//@ ensures (this.comm(other)==other.comm(this));
    public /*@ pure @*/ boolean comm(HasComm other){
        return false;
    }
}
