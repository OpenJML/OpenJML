// openjml -esc T_assume1.java
public class T_assume1 {
  //@ ensures a[\result] == 0;
  public int findZeroElement(int[] a) {
    int i = 0;
    for (; i < a.length; i++) {
      //@ assume 0 <= i < a.length;
      if (a[i] == 0) break;
    }
    //@ assume 0 <= i < a.length && a[i] == 0;
    return i;
  }
}
