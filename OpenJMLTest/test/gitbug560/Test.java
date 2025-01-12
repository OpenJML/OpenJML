public class Test {
   public static int k;
   
   //@ assignable k;
   //@ ensures k == 1;
   public void mm(/*@[B]@*/ A bbbb) {
       k = 1;
       bbbb.m();
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

    //@ also public normal_behavior
    //@   requires true;
    //@ pure
    public void m() {}

}
*/
