import p.X;
//@ model import q.X;

public class Test1 {
  X x; // OK
  p.X xx = x; // OK
  //@ ghost X y; // ERROR - ambiguous
}
