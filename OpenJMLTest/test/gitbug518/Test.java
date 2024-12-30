
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
        
        //@ refining signals (Exception e) e instanceof NullPointerException;
        {
        }
     }
     
    public void mmm(int f) {
        
        int eeeee;
        //@ refining
        //@ old boolean eeeee = f == 0;
        //@ ensures eeeee==0;
        {
            eeeee = 1;
            f = 1;
        }
     }
    
    //@ old int k = 0;
    //@ signals (Exception k) true;
    void p() {}
    
    void q(int k) {
        int k = 0;
    }
    
    void r() {
        int k;
        {
            int k;
        }
    }
    
    void t() {
        int e;
        try {
            r();
        } catch (Exception e) {
        }
    }
     
}