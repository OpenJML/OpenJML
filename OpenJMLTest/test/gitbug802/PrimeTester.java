public class PrimeTester {

    /*@ requires num >= 0;
      @ ensures \result <==> (\forall int i; 2 <= i < num; num % i != 0);
      @*/
    public /*@ pure @*/ static boolean isPrime(int num) {
        if (num < 2) {
            return false;
        }
        /*@ maintaining 2 <= i && i <= num;
          @ maintaining i > 2 ==> (\forall int j; 2 <= j < i; num % j != 0);
          @ decreases num - i;
          @*/
        for (int i = 2; i < num; i++) {
            if (num % i == 0) {
                return false;
            }
        }
        return true;
    }
}
