public class Test {

  public int i;

  //@ requires this.i == 0;
  //@ ensures this.i == 0;
  //@ ensures \old(this.i) == 0;
  public Test() {
    i = 0;
  }
}
