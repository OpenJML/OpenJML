public class T extends U {

  //@ requires i < 0;
  //@ also
  //@ requires i > 0;
  //@ behaviors complete; // ERROR
  public void m(int i) {}

  //@ requires i <= 0;
  //@ also
  //@ requires i >= 0;
  //@ also
  //@ requires i == 1; 
  //@ behaviors complete; // OK
  //@ behaviors disjoint; // ERROR - 2 combinations
  public void mcomplete(int i) {}

  //@ also
  //@ requires i < 2;
  //@ also
  //@ requires i < 3;
  //@ behaviors local_disjoint; // ERROR - just one pair
  public void mlocal(int i) {}

  //@ also
  //@ requires i < -3;
  //@ behaviors local_complete; // ERROR
  public void mlocal2(int i) {}

  //@ also
  //@ requires i < 0;
  //@ also
  //@ requires i > 0;
  //@ behaviors local_complete; // ERROR
  public void a(int i) {
    //@ assert i != 0; // SHOULD ALSO BE ERROR
  }
}

class U {

  //@ requires i > 0;
  public void mlocal(int i) {}

  //@ requires i > 0;
  public void mlocal2(int i) {}

  //@ requires i == 0;
  public void a(int i) {}
}
