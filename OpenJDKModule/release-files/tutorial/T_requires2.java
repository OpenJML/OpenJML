// openjml -esc -nullableByDefault T_requires2.java
public class T_requires2 {

  //@ requires a != null;
  //@ requires 0 <= index < a.length;
  //@ ensures \result == a[index];
  public int getElement(int[] a, int index) {
    return a[index];
  }
}
