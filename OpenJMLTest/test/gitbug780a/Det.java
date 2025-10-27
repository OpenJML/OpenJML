// A small check that there is no nullity problem with these arrays
abstract public class Det {

  //@ spec_pure
  abstract int [] theInt2();

  public void marray() {
    int [] x = theInt2();
  }

  }
