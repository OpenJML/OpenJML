// openjml -esc T_WellDefined2.java
public class T_WellDefined2 {
  int f;
  public void example(/*@ non_null */ T_WellDefined2 o) {
    //@ assert o.f == o.f;
  }
}
