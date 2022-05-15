class A {
    
  volatile public int x;

  public void testF() {
a:{}      int a = x;
b:{}      int b = x;
c:{}
    //@ assert a == \old(x,b); // OK
    //@ assert b == \old(x,c); // OK
    //@ assert a == b; // ERROR
  }
  public void testG() {
a:{}      int a = this.x;
b:{}      int b = this.x;
c:{}
    //@ assert a == \old(x,b); // OK
    //@ assert b == \old(x,c); // OK
    //@ assert a == b; // ERROR
  }
  public void testH() {
      boolean b = x == x;
      //@ assert x == x; // OK
      //@ assert b; // ERROR
  }
  
  //@ assigns x;
  //@ ensures \result == x;
  public int theX() {
      return x;
  }
  
  //@ assigns \nothing; // ERROR
  //@ ensures \result == x;
  public int badX() {
      return x;
  }
}
