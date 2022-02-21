public class BadMod {

  private
  //@ ghost static int f; // ERROR
  static void m1() {}
  
  public
  //@ requires true;  // ERROR
  public void m2() {}

  //@ public requires true; // ERROR - no modifiers allowed
  public void m3() {}

  public
  //@ normal_behavior ensures true; // ERROR
  public void m3() {}
  
  
  //@ public normal_behavior ensures true; // OK
  public void m4() {}
  
  public
  //@ invariant true; // ERROR
  
  public ; // ERROR
  
  //@ pure ; // ERROR

}
