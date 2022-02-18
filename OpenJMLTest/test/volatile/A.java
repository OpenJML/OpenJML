class A {
  //@ assignable \nothing;
  //@ ensures true;
  public int theIntPure();
  
  //@ ensures true;
  public int theInt();
  
  //@ assignable \nothing;
  //@ ensures true;
  //@ volatile
  public int nondeterministic();
  
  public void test() {
    int a = theIntPure(); // does not change heap
    int b = theIntPure();
    //@ assert a == b; // true
    int c = theInt(); // might change heap
    int d = theInt();
    //@ assert c == d; // not necessarily true
    int e = nondeterministic(); // no heap change, but volatile
    int f = nondeterministic();
    //@ assert e == f; // not necessarily true
  }
}
