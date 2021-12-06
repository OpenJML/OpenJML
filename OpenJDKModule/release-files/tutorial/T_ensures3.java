// openjml -esc T_ensures3.java
public class T_ensures3 {
  //@ requires a.length > 0;
  //@ ensures \result == a[0];
  public int fist(int[] a) {
    return a[0];
  }
}
