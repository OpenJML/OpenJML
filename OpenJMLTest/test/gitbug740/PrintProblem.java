public class PrintProblem {

    public static void main(String [] argv) {
        System.out.println("test starting...");
        test();
        System.out.println("... test done.");
    }

    //@ pure
    public static void test() {
        //@ assert 0 == 0;
    }
    
    public static void main1(String [] argv) {
        System.out.println("test starting...");
        test1();
        System.out.println("... test done."); // FAILURE -- test1 is assigns \everything
    }

    public static void test1() {
        //@ assert 0 == 0;
    }
}
