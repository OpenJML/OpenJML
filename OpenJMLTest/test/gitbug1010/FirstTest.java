
public class FirstTest {

    int a; //@ invariant a >= 0;

    //@ requires a < 0;
    public void setA(int a) { // ERROR: expcts an invariant failure at end of constructor
        this.a = a;
    }

    public String toString() {
        return ""+a;
    }

    public static void main(String[] args) {
        FirstTest x = new FirstTest();
        x.setA(10); // ERROR: Precondition failure
        System.out.println("x: "+x);
    }
}
