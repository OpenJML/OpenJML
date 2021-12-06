// openjml -esc T_arithmetic4.java
public class T_arithmetic4 {
  //@ requires i !=Integer.MIN_VALUE;
  //@ ensures \result >= 0;
  public int abs(int i) {
    return i>= 0 ? i : -i;
  }
}
