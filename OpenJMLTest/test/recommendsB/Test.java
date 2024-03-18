//@ nullable_by_default
public class Test {
    public int f;
    
    //@ recommends o != null else NullPointerException;
    public void m2(Test o) {
       o.f = 1;
    }
    
    //@ requires i >= 0;
    //@ recommends o != null else NullPointerException;
    //@ recommends i < 10 else ArrayIndexOutOfBoundsException;
    //@ requires i >= 0;
    //@ recommends o != null else NullPointerException;
    //@ recommends i < 10 else ArrayIndexOutOfBoundsException;
    public void m3(Test o, int i) {
        int[] a = new int[10];
        o.f = a[i];
    }
    
}