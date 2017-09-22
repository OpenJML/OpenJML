public class Test {
   public static int k;
   
   //@ pure 
   public void mm(/*@{B}*/ A b) {
       b.m();
   }
}


interface A {
    
    //@ public normal_behavior
    //@   requires true;
    //@   assignable \everything;
    public void m();
}

/*@ model
class B implements A {

    //@ public normal_behavior
    //@   requires true;
    //@ pure
    public void m() {}

}
*/