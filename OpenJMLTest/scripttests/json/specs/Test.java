public class Test {
    
    boolean b;
    // @ readable b if b;
    // @ writable b if b;

    //@ monitors_for b = k;
    int[] a = new int[9];
    
    //@ axiom b;
    //@ invariant b;
    //@ constraint \old(b) ==> b;
    //@ constraint \old(b) ==> b for m();
    // @ constraint \old(b) ==> b except m();
    
    //@ model int i;
    //@ represents i = b ? 0 : 1;
    
    int k; // @ in i;
       // @ maps k \into i;
    

    
    //@ ensures true;
    //@ static_initializer
    
    //@ ensures true;
    //@ initializer
}