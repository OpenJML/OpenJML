import java.lang.annotation.*;

public class ANN {
    public Object o, oo, ooo;

    boolean b = o instanceof @TTT ANN;
    // @ ghost boolean bb = oo instanceof @TTT ANN;
    //@ public invariant ooo instanceof @TTT ANN;
    // @ public invariant \exists @TTT ANN a; true; a != null;

  public void m(Object o) {
  }
}

@Target(ElementType.TYPE_USE)
@Retention(RetentionPolicy.RUNTIME)
@interface TTT {}

