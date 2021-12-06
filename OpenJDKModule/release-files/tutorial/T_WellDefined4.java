// openjml -esc T_WellDefined4.java
public class T_WellDefined4 {
  int f;
  public void example(/*@ nullable */ T_WellDefined4 o) {
    o.f = 0; // a Java statement
  }
}
