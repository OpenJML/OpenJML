// openjml -esc T_arithmetic3.java
public class T_arithmetic3 {
  //@ ensures \result >= 0;
  public int abs(int i) {
    return i>= 0 ? i : -i;
  }
}
