import p.*;
import static p.X.*;
//@ model import q.X;
//@ model import static q.X.Q;

public class Test2 {
  X x;
  p.X xx = x; // OK
  boolean q = Q;
  //@ ghost X y;
  //@ ghost q.X yy = y; // OK
  //@ ghost int qq = Q; // OK
}
