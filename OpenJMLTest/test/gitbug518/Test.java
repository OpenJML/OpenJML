
// Tests some scoping
public class Test {
    
    //@ signals (Exception e) e instanceof NullPointerException;
    public void m(int e) {
    }
    
    //@ old boolean e = f == 0;
    //@ requires e;
    public void mm(int e, int f) {
    }
    
    public void mmm() {
        
        int e;
        
        //@ signals (Exception e) e instanceof NullPointerException;
        {
        }
     }
     
    public void mmm(int f) {
        
        int e;
        
        //@ old boolean e = f == 0;
        //@ ensures e;
        {
            e = 1;
            f = 1;
        }
     }
     
}