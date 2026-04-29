public class EscFileB {

    //@ requires x != 0;
    //@ ensures \result * x == 1 || \result == 0;
    public int sign(int x) {
        return x > 0 ? 1 : -1;
    }

    //@ requires a >= b;
    //@ ensures \result == a - b;
    public int diff(int a, int b) {
        return a - b;
    }

    //@ requires n > 0;
    //@ ensures \result >= 0 && \result < n;
    public int mod(int x, int n) {
        return ((x % n) + n) % n;
    }
}
