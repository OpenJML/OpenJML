/**
 * Sample Java class with JML specifications used by the OpenJML VS Code UI tests.
 * Each method has specs so that ESC code lenses appear after a --check run.
 */
public class Sample {

    //@ requires x >= 0;
    //@ ensures \result >= 0;
    //@ ensures \result == x || \result == -x;
    public int abs(int x) {
        return x >= 0 ? x : -x;
    }

    //@ requires x >= 0 && y >= 0;
    //@ ensures \result == x + y;
    public int add(int x, int y) {
        return x + y;
    }

    //@ requires n >= 0;
    //@ ensures \result >= 1;
    public long factorial(int n) {
        long result = 1;
        for (int i = 2; i <= n; i++) {
            result *= i;
        }
        return result;
    }  
}
