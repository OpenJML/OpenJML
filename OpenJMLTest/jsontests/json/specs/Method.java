public class Method {
    


    
    //@ public normal_behavior
    //@   requires b;
    //@   requires b else RuntimeException;
    //@   old boolean bb = b;
    //@   writes b, this.b, this.*, super.x, a[0], a[1..2], a[*], a[2..], \nothing, \everything;
    //@   ensures b;
    //@   callable \nothing;
    //@   callable \everything;
    //@   callable m(int);
    //@   {|
    //@      ensures true;
    //@   also
    //@      ensures false;
    //@   |}
    //@   duration 4242 if true;
    //@   
    //@ also public behavior
    //@   signals (Exception e) true;
    //@   signals (Exception) true;
    //@   signals_only \nothing;
    //@   signals_only RuntimeException;
    //@ behaviors complete;
    
    public void m(int k) {
        //@ ghost var z = (1,"",true);
        //@ assume k == 0;
        //@ assert b;
        //@ check b;
        //@ show b;
        //@ set b = false;
        
        //@ loop_invariant true;
        //@ loop_assigns \nothing;
        //@ loop_writes z;
        //@ loop_decreases k;
        while (true) {}
    }
    
    
}