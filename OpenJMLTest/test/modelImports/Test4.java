import p.*;
//@ model import q.*;

public class Test4 {
  X x;                   // OK
  p.X xx = x;            // OK
  Y z;                   // ERROR
  //@ ghost X y;         // ERROR - ambiguous
  //@ ghost q.X yy = y;  // OK
  //@ ghost Y zz;        // OK
  //@ ghost q.Y zzz = zz; // OK
}
