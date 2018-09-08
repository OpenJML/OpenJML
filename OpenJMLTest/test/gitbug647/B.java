//@ non_null_by_default
class A {
    //@ spec_public
    private String s;
    
    //@ private normal_behavior
    //@   requires true;
    //@ pure
    public A() {
        s = "hello";
    }
}
//@ non_null_by_default
public class B {
    //@ public normal_behavior
    //@   requires true;
    //@ pure
    public B(A a) {
        //@ assert a.s != null;  // OpenJML reports error
    }
    
    //@ public normal_behavior
    //@   requires true;
    //@ pure
    public void testMethod(A a) {
        //@ assert a.s != null;  // fine
    }
}