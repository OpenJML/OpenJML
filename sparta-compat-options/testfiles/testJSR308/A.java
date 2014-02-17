public class A {

    static void m() {
        //@ assert true;
    }
    
    public static void r(byte [] /*@Sink(DATABASE)*/ b){
    }
   
}