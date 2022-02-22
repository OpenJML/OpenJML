public class Test {

  //@ pure
  public int doA(int i) { return 1; }

  //@ ensures doA(x) == doA(y);
  public void test1(int x, int y) {  }
  
  //@ ensures doA(x) == doA(x);
  public void test2(int x, int y) {  }
  
  //@ requires x == y;
  //@ ensures doA(x) == doA(y);
  public void test3(int x, int y) {  }
  
  //@ requires y <= x <= y;
  //@ ensures doA(x) == doA(y);
  public void test4(int x, int y) {  }

}
  
