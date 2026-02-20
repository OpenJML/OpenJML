//@ nullable_by_default
abstract public class PF {

  public int v;
  //@ ensures this.v == i;
  public PF(int i) { v = i; }

  //@ public normal_behavior
  //@ ensures \result != null;
  //@ ensures \result.v == i;
  //@ pure
  abstract public PF x(int i);

  //@ public normal_behavior
  //@  { return x(0); }
  //@ pure
  abstract public PF x();


  //@ requires s != null;
  //@ ensures \result != null ;
  //@ ensures \result.v == 0;
  public PF m(PF s) {
    return s.x();
  }
}
    
//@ nullable_by_default
abstract class PFF {

  public int v;
  //@ ensures this.v == i;
  public PFF(int i) { v = i; }

  //@ public normal_behavior
  //@ ensures \result != null;
  //@ ensures \fresh(\result);
  //@ ensures \result.v == i;
  //@ pure
  abstract public PFF x(int i);

  //@ public normal_behavior
  //@  { return x(0); }
  //@ pure
  abstract public PFF x();


  //@ requires s != null;
  //@ ensures \result != null ;
  //@ ensures \fresh(\result);
  //@ ensures \result.v == 0;
  public PFF mm(PFF s) {
    return s.x();
  }
}
    
