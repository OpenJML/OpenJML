// This just makes sure that the various framing synonyms are all recognized
public class Test {

  public int i;

  //@ assignable i;
  //@ assigns i;
  //@ writes i;
  //@ accessible i;
  //@ reads i;
  public void m() {}
}
