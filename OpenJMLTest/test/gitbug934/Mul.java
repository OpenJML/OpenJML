public class Mul {
    //@ requires (x > 0 && y < 0) || (x < 0 && y > 0);
    //@ ensures \result == x * y;
    public static int Mul(int x, int y) {
        return x * y;
    }
}
