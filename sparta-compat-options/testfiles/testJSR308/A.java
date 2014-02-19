public class A {

    static void m() {
        //@ assert true;
    }
    //@Sink(DATABASE)
    public static void r(byte [] /*@Sink(DATABASE)*/ b){
    }
   
}