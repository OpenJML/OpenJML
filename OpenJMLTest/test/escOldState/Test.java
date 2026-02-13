// Tests of old clauses in nested behaviors
public class Test {
    
    public int b;
    
    //@ public normal_behavior
    //@   requires a == 0 && b == 0;
    //@   assigns b;
    //@   ensures b == 10;
    //@   ensures \old(b) == 0;
    public void mmm(int a) {
        a = 1;
        a = 2;
        b = 2;
        //@ check a == \old(a) + 2;
        
        for (int k = 0; k < 10; k++) {
            //@ check \old(b) == 0; // \Old is still the pre-state of the method
        }

        //@ refining
        //@   assigns a, b;
        //@   ensures \old(b) == 2;
        //@   ensures b == 5;
        {
          a = 3; b = 3;
          //@ check \old(a) == 2;
          for (int k = 0; k < 10; k++) {
              //@ check \old(b) == 2; // \Old is still the pre-state of the refining block
          }

          //@ refining
          //@   assigns a, b;
          //@   ensures \old(b) == 3;
          //@   ensures b == 5;
          {
              b = 5;
              //@ check \old(b) == 3;
              //@ check b == 5;
          }
          
          //@ check \old(b) == 2;
          //@ check b == 5;
        }
        qq();
    }
    
    //@ public normal_behavior
    //@   requires b == 5;
    //@   assigns b;
    //@   ensures b == 10;
    //@   ensures \old(b) == 5;
    public void qq() {
        b = 10;
    }
}