public class Prime {

 public static /*@ pure helper @*/ boolean is_prime(int n) {
    int maxInt = ((Double) Math.ceil(Math.sqrt(n))).intValue();
    for (int i = 0; i <= maxInt; i++) {
        if ((n%i)==0) {
            return false;
        }
    }
    return true;
}
}