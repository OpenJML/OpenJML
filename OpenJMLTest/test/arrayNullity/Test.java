import org.jmlspecs.annotation.*;

//@ nullable_by_default
public class Test {

  public void m1() {
    @NonNull Object[] o; // OK - onlyelements are null
    o = null; // OK
  }

  public void m2() {
    @NonNull Object[] o = new Object[10]; // ERROR - null elements
    o[0] = null; // ERROR
  }

  public void m3() {
    Object @NonNull[] oo;
    oo = null; // ERROR
  }

  public void m4() {
    Object @NonNull[] oo = new Object[10];
    oo[0] = null; // OK
  }

}

