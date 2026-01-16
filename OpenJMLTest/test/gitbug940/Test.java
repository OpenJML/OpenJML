public class Test {

  public void m(String s) {
    s = "a";
    //@ assert \old(s).length() == \old(s.length());
  }
}
