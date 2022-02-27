public class AddLoop {
    //@ requires y > 0;
    //  requires Integer.MIN_VALUE <= x + y && x + y <= Integer.MAX_VALUE && y !=
    // Integer.MIN_VALUE;
    //@ ensures \result == x + y;
    public int addLoop(int x, int y) {
        int sum = x;
        int n = y;
        while (n > 0) {
            sum = sum + 1;
            n = n - 1;
        }
        return sum;
    }
}
