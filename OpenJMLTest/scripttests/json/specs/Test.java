public class Test {
    
    boolean b;

    int[] a = new int[9];

    //@ readable b if b;
    //@ writable b if b;
    //@ monitors_for b = k;

    //@ axiom b;
    //@ invariant b;
    //@ constraint \old(b) ==> b;
    //@ constraint \old(b) ==> b for m();
    //@ constraint \old(b) ==> b for ! m();
    
    //@ model int i;
    //@ represents i = b ? 0 : 1;
    
    int k;
      // @ in i;
       // @ maps k \into i;
    

    
    //@ ensures true;
    //@ static_initializer
    
    //@ ensures true;
    //@ initializer
    
    //@ ghost \bigint ii;
    //@ model \real jj;
    //@ ghost \set<Object> oo;
    
    public void m1(Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {
        //@ loop_invariant a.values == \old(a.values);
        //@ inlined_loop;
        a.forEach(MMM::bump);
    }
}