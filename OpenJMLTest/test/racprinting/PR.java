//@ nullable_by_default
public class PR { 

  int ff = 99;

  public static void main(String ... args) {
    //@ ghost \bigint b = 100;
    long k = 42;
    String s = "Z";
    PR p = new PR();
    //@ print "PRINTING", s, 2*b, k+8, 7, null, p.ff, false, k>0;
    p = null;
    try {
    //@ print "NULL?", p, p.ff;
    } catch (Exception e) {}
    //@ print "DONE";
  }
}
