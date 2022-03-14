public class AddLoop {
    //@ requires y > 0;
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
