// This is a case where overapproximation of a method causes feasibility
// testing to falsely say a statement is reachable
class C {
  //@ normal_behaviour
  //@  ensures \result >= 0;
  static int zero() { return 0; }

  void m() {
    int i = zero();
    if (i==42) { /*@ reachable ; */ }
  }
}
