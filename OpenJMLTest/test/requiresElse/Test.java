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
}