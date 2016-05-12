package demo.strongarm;

/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, locals in branches
 * 
 * @author jls
 *
 */
public class A3 {
    
    //@ requires true;
    public int localTest(int a, int b){
        
        int c = a;
        
        if(c > -1){
            return 0;
        }
        
        return -1;
    }
    
    
}

