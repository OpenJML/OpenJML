// openjml -esc T_WellDefined3.java
public class T_WellDefined3 {
  int f;
  public void example(/*@ nullable */ T_WellDefined3 o) {
    //@ assert o.f == o.f;
  }
}
