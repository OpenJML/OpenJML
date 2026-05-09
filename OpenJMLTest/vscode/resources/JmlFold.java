/**
 * Java file with multi-line JML block comments used for folding tests.
 * Each method has a long /*@ ... @*‌/ block so that a folding range provider
 * should offer at least one range per method.
 */
public class JmlFold {

    /*@ requires x >= 0;
      @ requires x <= Integer.MAX_VALUE / 2;
      @ ensures \result >= 0;
      @ ensures \result * \result <= x;
      @ pure
      @*/
    public int isqrt(int x) {
        int r = (int) Math.sqrt(x);
        while ((long)(r + 1) * (r + 1) <= x) r++;
        while ((long) r * r > x) r--;
        return r;
    }

    /*@ requires a != null;
      @ requires b != null;
      @ requires a.length == b.length;
      @ ensures \result.length == a.length;
      @ ensures (\forall int i; 0 <= i && i < \result.length;
      @           \result[i] == a[i] + b[i]);
      @*/
    public int[] vectorAdd(int[] a, int[] b) {
        int[] result = new int[a.length];
        for (int i = 0; i < a.length; i++) result[i] = a[i] + b[i];
        return result;
    }

    //@ requires n > 0;
    //@ ensures \result > 0;
    public int simple(int n) { return n; }
}
