public class TestRefines {
    
    //@ requires 0 <= i <= 100;
    //@ ensures \result >= 11;
    public int m1(int i) {
        
        int j = 0;
        //@ refining
        //@ assignable j;
        //@ ensures j >= 11;
        //@ begin
        j = i + 10;
        j++;
        //@ end
        return j;
    }
    
    //@ requires 0 <= i <= 100;
    //@ ensures \result >= 11;
    public int m2(int i) {
        
        int j = 0;
        //@ assignable j;
        //@ ensures j >= 11;
        {
        j = i + 10;
        j++;
        }
        return j;
    }
    
    
    
    
    
}