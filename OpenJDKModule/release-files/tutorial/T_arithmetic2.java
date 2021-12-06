// openjml -esc T_arithmetic2.java
public class T_arithmetic2 {
  //@ requires i < Integer.MAX_VALUE;
  //@ ensures \result == i+1;
  public int increment(int i) {
    return i+1;
  }
}
