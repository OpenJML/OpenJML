public class Test {
    
    public int i;
    public short j;

    public void m() {
        i = 5;
        j = 6;
        //@ havoc this.*;
        //@ check Short.MIN_VALUE <= j <= Short.MAX_VALUE;
        //@ check i == 5; // ERROR
        //@ check j == 6; // ERROR
    }
}