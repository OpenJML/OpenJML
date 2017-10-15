public class Test {
    
   //@ pure 
   public void mm(B b) {
       b.m();
   }
}


interface A {
    
    //@ public normal_behavior
    //@   requires true;
    //@   assignable \everything;
    public void m();
}

class B implements A {

    //@ public normal_behavior
    //@   requires true;
    //@   assignable \nothing;
    public void m();

}