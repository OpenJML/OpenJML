import static p.X.Q;   // Q is boolean
//@ model import static q.X.Q; // Q is int

public class Test5 {
  boolean qq = Q;
  //@ ghost int qqq = Q;
  //@ ghost boolean b = Q;
}
