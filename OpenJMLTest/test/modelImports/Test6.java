import p.*;
import static p.X.*;
//@ model import q.X;
//@ model import static q.X.Q;

public class Test6 {
  X x;
  p.X xx = x; // OK
  boolean q = Q; // ERROR
  //@ ghost X y;
  //@ ghost q.X yy = y; // OK
  //@ ghost int qq = Q; // OK // Bug - does not see the static import
}
