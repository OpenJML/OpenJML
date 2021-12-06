// openjml -esc T_arithmetic1.java
public class T_arithmetic1 {
  //@ ensures \result == i+1;
  public int increment(int i) {
    return i+1;
  }
}
