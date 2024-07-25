public class T {

  //@ requires i > 0;
  //@ also
  //@ requires i < 0;
  //@ behaviors complete;
  public void m(int i) {}

  //@ requires true;
  //@ behaviors complete;
  //@ behaviors local_complete;
  //@ behaviors disjoint;
  public void more() {}

  //@ requires true;
  //@ behaviors zzz;
  public void mbad1() {}

  //@ requires true;
  //@ behaviors disjoint  // no semicolon
  public void mbad2() {}

  //@ requires true;
  //@ behaviors ;
  public void mbad3() {}

  //@ requires true;
  //@ behaviors 
  public void mbad4() {}
}
