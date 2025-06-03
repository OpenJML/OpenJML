abstract public class Det {

  //@ pure
  abstract int theInt();

  //@ spec_pure
  abstract int /*@ non_null */ [] theInt2();

  public void m() {
    int x = theInt();
    //@ assert theInt() == theInt();
    //@ assert x == theInt();
    int y = theInt();
    //@ assert x == y;
  }

  public void marray() {
    int/*@ non_null */ [] x = theInt2();
    //@ assert theInt2() == theInt2();
    //@ assert java.util.Arrays.equals(theInt2(), theInt2());
    //@ assert x == theInt2();
    //@ assert java.util.Arrays.equals(x, theInt2());
    int /*@ non_null */ [] y = theInt2();
    //@ assert x == y;
    //@ assert java.util.Arrays.equals(x, y);
  }

  //@ model public int nullable[] myIntArray;

  //@ ensures java.util.Arrays.equals(\result, myIntArray);
  //@ spec_pure
  abstract int/*@ non_null */[] theInt3();

  public void mmodel() {
    int/*@ non_null */ [] x = theInt3();
    //@ assert java.util.Arrays.equals(theInt3(), theInt3());
    //@ assert java.util.Arrays.equals(x, theInt3());
    int/*@ non_null */[] y = theInt3();
    //@ assert java.util.Arrays.equals(x, y);
  }
 
  //@ ensures \result == myIntArray;
  //@ spec_pure
  abstract int/*@ non_null */[] theInt4();

  public void mmodel2() {
    int/*@ non_null */[] x = theInt4();
    //@ assert theInt4() == theInt4();
    //@ assert java.util.Arrays.equals(theInt4(), theInt4());
    //@ assert x == theInt4();
    //@ assert java.util.Arrays.equals(x, theInt4());
    int/*@ non_null */[] y = theInt4();
    //@ assert x == y;
    //@ assert java.util.Arrays.equals(x, y);
  }
}
