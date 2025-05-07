import p.X;
//@ model import q.*;

public class Test3 {
  X x;
  Y y; // ERROR
  p.X xx = x; // OK
  //@ ghost X y;
  //@ ghost p.X z = y; // OK
  //@ ghost Y yy;      // OK
  //@ ghost q.Y zz = yy; // OK
}
