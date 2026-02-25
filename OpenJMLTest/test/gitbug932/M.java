public class M {
  public static void main(String... args) {
    int k = new Super().m();
    //@ check k == 42;
    //@ print "DONE";
  }
}

class Super extends A {
  //@ also public normal_behavior
  //@ ensures \result == super.m();
  //@ ensures \result == 43; // ERROR
  //@ spec_pure
  public int m() {
    return super.m();
  }
}

class A {
  //@ public normal_behavior
  //@ ensures \result == 42;
  //@ spec_pure
  public int m() {
    return 42;
  }
}
