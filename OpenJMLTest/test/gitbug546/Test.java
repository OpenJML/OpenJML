public interface Test {

  //@ requires b;
  public void mok(boolean b);

  //@ requires b;
  //@ requires !b;
  public void mbad(boolean b);
}

class T {

  //@ requires false;
  //@ model void qbad();

  //@ requires true;
  //@ model void qok();

  //@ ensures true;
  //@ model void rok();

  //@ ensures false;
  //@ model void rr();

  //@ model void rrr() {
  //@  //@ set rr();
  //@ }
}
