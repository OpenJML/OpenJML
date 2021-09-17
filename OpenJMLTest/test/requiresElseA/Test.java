//@ nullable_by_default
public class Test {
    public int f;
    
    //@ recommends o != null ;
    public void m1(Test o) {
       if (o == null) throw new NullPointerException();
    }
    
}