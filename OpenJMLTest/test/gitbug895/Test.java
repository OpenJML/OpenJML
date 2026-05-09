//@ pure
public class Test extends T {

   public int m() { return 1; }

}

class T {

  //@ spec_pure
  public int m() { return 0; }

}
