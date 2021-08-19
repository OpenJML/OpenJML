public interface HasComm {
  //@ ensures (\result==other.comm(this));
  /*@ pure @*/ boolean comm(HasComm other);
}
