// Simple case of using static method of non-static inner class
public class X {

  public class N {

    //@ public normal_behavior
    //@  ensures \result == 123;
    //@ spec_pure
    public static int k() { return 123; }

  }
}

class Y {
  static int k;

  //@ requires k == X.N.k();
  //@ ensures  k == X.N.k();
  static void m() {
    int z = X.N.k();
  }
}


