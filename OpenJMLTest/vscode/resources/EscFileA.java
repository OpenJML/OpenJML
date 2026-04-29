public class EscFileA {

    //@ requires x >= 0;
    //@ ensures \result >= 0;
    public int abs(int x) {
        return x < 0 ? -x : x;
    }

    //@ requires a >= 0 && b >= 0;
    //@ ensures \result == a + b;
    public int add(int a, int b) {
        return a + b;
    }

    //@ requires n >= 0;
    //@ ensures \result >= 1;
    public int factorial(int n) {
        return n == 0 ? 1 : n * factorial(n - 1);
    }
}
