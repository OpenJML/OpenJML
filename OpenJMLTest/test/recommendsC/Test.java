//@ nullable_by_default
public class Test {
    public int f;
    
    //@ recommends o != null else NullPointerException;
    public void m1(Test o) {
       if (o == null) throw new NullPointerException();
    }
    
    public void m2() {
        m1(null);
    }
    
    public void m3(/*@ non_null*/ Test o) {
        //@ assert o != null;
        m1(o);
    }
    
}