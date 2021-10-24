// openjml -esc T_ensures1a.java
public class T_ensures1a {
  //@ ensures \result == a | \result == b | \result == c | \result == d;
  //@ ensures \result >= a & \result >= b & \result >= c & \result >= d;
  public int max(int a, int b, int c, int d) {
    if (a >= b && a >= c && a >= d) return a;
    if (b >= a && b >= c && b >= d) return b;
    if (c >= a && c >= b && c >= d) return c;
    return d;
  }
}
