// openjml -esc T_arithmetic5.java
public class T_arithmetic5 {
  //@ ensures \result == \java_math(i+1);
  //@ code_java_math
  public int m(int i) { 
    return i+1;
  }
}
