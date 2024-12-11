// This version of issue #650 has the axiom within the Content class - it doesn't parse correctly
interface A {
    /*@ immutable pure public static model class Content {
      @     public normal_behavior
      @       ensures true;
      @     no_state
      @     public boolean P(nullable Object key);

      @ axiom (\forall Content c; (\forall Object o; c.P(o)));

      @ }
      @
      @*/
    
    //@ public model instance non_null Content content;

    //@ public invariant content.P(null);
}
public final class B {
    public B(/*@ non_null */ A a) {
        this.a = a;
    }
    

    public /*@ non_null */ A a;
        
    //@ public normal_behavior
    //@   ensures true;
    public void testMethod() {
    }
}
