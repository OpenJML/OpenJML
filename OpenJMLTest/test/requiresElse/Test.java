public class Test {
    
    //@ public normal_behavior
    //@ requires i >= 0 else IllegalArgumentException;
    //@ ensures \result == 0;
    public int mtest(int i) {
        if (i < 0) throw new IllegalArgumentException();
        return 0;
    }

    //@ requires i < 10 else IllegalArgumentException;
    //@ ensures \result >= 0;
    //@ also
    //@ ensures \result == 0;
    //@ requires i >= 0 else IllegalArgumentException;
    public int mtest2(int i) {
        if (i >= 10) throw new IllegalArgumentException();
        if (i < 0) throw new IllegalArgumentException();
        return 0;
    }

    public int j = 0;

    //@ requires i < 10 else IllegalArgumentException;
    //@ requires i > 0 else NullPointerException;
    //@ writes j;
    //@ ensures \result == 0;
    public int mtest3(int i) {
      if (i >= 10) throw new IllegalArgumentException();
      if (i <= 0) throw new NullPointerException();
      j = 1;
      return 0;
    }

    //@ requires i > 10;
    //@ {|
    //@   requires i > 11;
    //@ also
    //@   requires i > 12;
    //@ |}
    //@ requires i > 20;
    //@ ensures \result == 0;
    //@ pure
    public int mtest4(int i) {
        return 0;
    }

    //@ requires i > 10;
    //@ {|
    //@   requires i > 11;
    //@ also
    //@   requires i > 12;
    //@ |}
    //@ requires i > 20;
    //@ signals_only \nothing;
    //@ ensures \result == 0;
    //@ pure
    public int mtest5(int i) {
        return 0;
    }
    

    //@ requires i < 10 else IllegalArgumentException;
    //@ recommends i > 0 else NullPointerException;
    //@ writes j;
    //@ ensures \result == 0;
    public int mtest6(int i) {
      if (i >= 10) throw new IllegalArgumentException();
      if (i <= 0) throw new NullPointerException();
      j = 1;
      return 0;
    }
}
