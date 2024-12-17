abstract public class Det {

  //@ pure
  abstract int theInt();

  //@ pure
  abstract int[] theInt2();

  public void m() {
    int x = theInt();
    //@ assert theInt() == theInt();
    //@ assert x == theInt();
    int y = theInt();
    //@ assert x == y;
  }

  public void marray() {
    int[] x = theInt2();
    //@ assert theInt2() == theInt2();
    //@ assert java.util.Arrays.equals(theInt2(), theInt2());
    //@ assert x == theInt2();
    //@ assert java.util.Arrays.equals(x, theInt2());
    int[] y = theInt2();
    //@ assert x == y;
    //@ assert java.util.Arrays.equals(x, y);
  }

  //@ model public int nullable[] myIntArray;

  //@ ensures java.util.Arrays.equals(\result, myIntArray);
  //@ pure
  abstract int[] theInt3();

  public void mmodel() {
    int[] x = theInt3();
    //@ assert java.util.Arrays.equals(theInt3(), theInt3());
    //@ assert java.util.Arrays.equals(x, theInt3());
    int[] y = theInt3();
    //@ assert java.util.Arrays.equals(x, y);
  }
 
  //@ ensures \result == myIntArray;
  //@ pure
  abstract int[] theInt4();

  public void mmodel2() {
    int[] x = theInt4();
    //@ assert theInt4() == theInt4();
    //@ assert java.util.Arrays.equals(theInt4(), theInt4());
    //@ assert x == theInt4();
    //@ assert java.util.Arrays.equals(x, theInt4());
    int[] y = theInt4();
    //@ assert x == y;
    //@ assert java.util.Arrays.equals(x, y);
  }
}
