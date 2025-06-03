public class Test {
    
    boolean b;
    int[] a = new int[9];
    
    //@ axiom b;
    //@ invariant b;
    //@ constraint \old(b) ==> b;
    // @ constraint \old(b) ==> b for m();
    // @ constraint \old(b) ==> b except m();
    
    //@ model int i;
    //@ represents i = b ? 0 : 1;
    
    int k; // @ in i;
       // @ maps k \into i;
    
    // @ readable b if b;
    // @ writable b if b;
    
    
    //@ public normal_behavior
    //@   requires b;
    //@   requires b else RuntimeException;
    // @   writes b, this.b, this.*, a[0], a[1..2], a[*], a[2..], \nothing, \everything;
    //@   ensures b;
    //@   
    //@ also public behavior
    //@   signals (Exception e) true;
    //@   signals (Exception) true;
    //@   signals_only \nothing;
    //@   signals_only RuntimeException;
    //@ behaviors complete;
    
    public void m(int k) {
        //@ ghost int z = 0;
        //@ assume k == 0;
        //@ assert b;
        //@ check b;
        //@ show b;
        //@ set b = false;
        
        //@ loop_invariant true;
        // @ loop_assigns \count;
        //@ loop_decreases k;
        while (true) {}
    }
    
}