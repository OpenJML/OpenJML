import p.*;
//@ model import q.X;

public class Test2 {
  X x;
  p.X xx = x; // OK
  //@ ghost X y;
  //@ ghost q.X yy = y; // OK
}
