//@ nullable_by_default
public class A  {
  static public int i;
  //@ ghost static public int k;

  public static void main(String... args) { 
    /*@ assert args.length >= 0; */
    i = 0;
    m(9); 
  } 
 
  //@ requires k == 0;
  //@ requires add(0);
  /*@ ensures \result == y;  */  
  public static int m(int y) { 
    //@ assert i == k && (i == 9); 
    add(0);
    return y;
  } 
 
  //@ model public static pure boolean g(int g, Object o);

  //@ pure
  public static boolean add(int z) {
    //@ ghost \bigint i = Integer.MAX_VALUE;
    //@ ghost var j = 2*i;
    return true;
  }
}
