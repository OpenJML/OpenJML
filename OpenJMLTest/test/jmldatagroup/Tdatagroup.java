public class Tdatagroup {
    
    //@ model public \datagroup m;
    
    public int i; //@ in m;
    public int j;
    
    //@ assigns m;
    public void q() {
        i = 0;
    }
    
    //@ assigns m;
    public void qbad() {
        j = 0; // ERROR
    }
    
    public static void main(String ... args) {
        new Tdatagroup().q(); new Tdatagroup().qbad();
    }
}