import org.jmlspecs.annotation.NonNullByDefault;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.Pure;


@NonNullByDefault
public class FreshBugs {
    static class Node {
        Object payload_;
        @Nullable Node next_;
        //@ ensures payload_ == payload && next_ == next;
        //@ pure
        Node(Object payload, /*@ nullable */ Node next){
            payload_ = payload;
            next_ = next;
        }
        //@ ensures payload_ == payload && next_ == null;
        // No pure on purpose
        Node(Object payload){
            payload_ = payload;
            next_ = null;
        }
    }
    @Nullable Object o = new Object();
    Object oo = new Object(); // oo is non_null
   
    /*@
      requires o != null;
      ensures \fresh(\result);
      ensures !\fresh(\result.payload_); // OK
    */
     Node ok_test0() {
        Node n = new Node(o, null);
        return n;
    }
     
    /*@
     ensures \fresh(\result);
     ensures \fresh(\result.payload_); // ERROR
    */
    Node fail_test0() {
       Node n = new Node(oo, null);
       return n;
    }
    
    /*@
       ensures \fresh(\result);
     */
     Node fresh_bug() { // FAILS, because Node writes \everything, including oo, so oo is possibly null
       Node n = new Node(new Object());
       return n;
     }

    
    /*@
      ensures \fresh(\result);
      ensures \fresh(\result.payload_);
    */
    Node fail_test1() {
        Node n = new Node(new Object(), null);
        return n;
    }
    /*@
      ensures \fresh(\result);
      ensures \fresh(\result.payload_);
    */
    Node fail_test2() {
        Object o = new Object();
        Node n = new Node(o, null);
        return n;
    }


    /*@
      ensures \fresh(\result);
    */
    FreshBugs good_test3() {
        return new FreshBugs(); //noargs...
    }

    static class IntContainer {
        int i_=0;
        //@ ensures i_ == i;
        //@ pure
        IntContainer(int i) {
            i_=i;
        }
    }
    /*@
      ensures \fresh(\result);
    */
    IntContainer fail_test4() {
        return new IntContainer(1); //even a non-ref arg fails
    }

}
