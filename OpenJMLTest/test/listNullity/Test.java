import java.util.*;
import org.jmlspecs.annotation.*;

//@ nullable_by_default
public class Test {

  public void m1(@NonNull Integer i) {
    List<@NonNull Integer> lst = new LinkedList<>();
    lst.add(i); // OK
    lst.add(null); // ERROR
  }

  public void m2(@NonNull Integer i) {
    List<@Nullable Integer> lst = new LinkedList<>();
    lst.add(i); // OK
    lst.add(null); // OK
  }

  public void m3(Integer i) {
    List<@Nullable Integer> lst = new LinkedList<>();
    lst.add(i); // OK
    lst.add(null); // OK
  }

  public void m4(Integer i) {
    List<Integer> lst = new LinkedList<>();
    lst.add(i); // OK
    lst.add(null); // OK
  }

  //@ non_null_by_default
  public class Inner {

  public void m5(Integer i) {
    List<Integer> lst = new LinkedList<>();
    lst.add(i); // OK
    lst.add(null); // ERROR
  }

  public void m6(@Nullable Integer i) {
    List<Integer> lst = new LinkedList<>();
    lst.add(i); // ERROR
  }

  }

}
