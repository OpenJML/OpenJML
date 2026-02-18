public class MaxBad {

  //@ ensures \result >= i && \result >= j && \result >= k;
  //@ ensures \result == i || \result == j || \result == k;
  public static int max(int i, int j, int k) {
    int t = i > j ? i : j;
    return t > k ? i : k;
  }
}
