// openjml -esc -nullableByDefault T_requires3.java
public class T_requires3 {

  //@ requires 0 <= index < a.length;
  //@ requires a != null;
  //@ ensures \result == a[index];
  public int getElement(int[] a, int index) {
    return a[index];
  }
}
