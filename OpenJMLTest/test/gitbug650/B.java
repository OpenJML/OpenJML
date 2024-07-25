// This is the original #650b problem
interface A {
    /*@ immutable pure public static model class Content {
      @     public normal_behavior
      @       ensures true;
      @     no_state
      @     public boolean P(nullable Object key);

      @ }
      @
      @ axiom (\forall Content c; (\forall Object o; c.P(o)));
      @*/
    
    //@ public model instance non_null Content content;

    //@ public invariant content.P(null);
}
public final class B {
    public B(/*@ non_null */ A a) {
        this.a = a;
    } // Fails to prove invariant above because solver does not know whether result of P
      // depends on B.a, but the axiom states the needed predicate
    

    public /*@ non_null*/A a;
        
    //@ public normal_behavior
    //@   ensures true;
    public void testMethod() {
    }
}
