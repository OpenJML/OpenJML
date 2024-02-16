public class T {

  //@ requires i < 0;
  //@ also
  //@ requires i > 0;
  //@ behaviors complete;
  public void m(int i) {}

  //@ requires i <= 0;
  //@ also
  //@ requires i >= 0;
  //@ also
  //@ requires i == 1;
  //@ behaviors complete;
  //@ behaviors disjoint;
  public void mcomplete(int i) {}

}
