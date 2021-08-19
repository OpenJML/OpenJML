public class Main {
    public static void main(String [] argv) {
        HasComm a = new A();
        HasComm b = new B();
        //@ assert a.comm(b) == b.comm(a);  // ESC says this is valid!
        //@ assert a.comm(b) != b.comm(a);  // ESC can't prove this
        System.out.println("a.comm(b) is " + a.comm(b));
        System.out.println("b.comm(a) is " + b.comm(a));
        System.out.println("a.comm(b) == b.comm(a) is "
                           + (a.comm(b) == b.comm(a)));
    }
}
