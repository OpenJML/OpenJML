public class Q {

  //@ ensures \result == i;
  public int m(int i) {
    return i;
  }


  //@ ensures \result == 1;
  public int q() {
    return 0;
  }
}
