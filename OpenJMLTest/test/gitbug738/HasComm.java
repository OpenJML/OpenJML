public interface HasComm {
  //@ ensures (this.comm(other)==other.comm(this));
  /*@ pure @*/ boolean comm(HasComm other);
}
