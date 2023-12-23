public class SquareRoot {

    //@ requires n >= 0;
    //@ requires (n+1) * (n+1) < Integer.MAX_VALUE;
    //@ ensures 0 <= \result * \result <= n < (\result + 1)*(\result + 1);
    public static int squareRoot(int n) {
        int a = 0;
        //@ maintaining (a+1)*(a+1) < Integer.MAX_VALUE;
        while(!(n < (a+1)*(a+1))) {
            a++;
        }
        //@ assert 0 <= a*a <= n < (a+1)*(a+1);
        return a;
    }

    // Uncomment below to test algorithm
    /*
    public static void main(String[] args) {
        for (int i = 0; i < 200; i ++) {
            if (Math.floor(Math.sqrt(i)) != squareRoot(i)) {
                System.out.printf("fail: Math.sqrt(%d)=%f, squareRoot(%d)=%d\n", i, Math.sqrt(i), i, squareRoot(i));
            }
        }    
    }
    */
}
