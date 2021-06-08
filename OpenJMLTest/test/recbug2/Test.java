public class Test {

  //@ ensures \result == g();
  //@ pure
  public boolean f() { return true; }

  //@ ensures \result == f();
  //@ pure
  public boolean g() { return true; }

}
