public class Test {

  //@ requires s.length() == 10;
  public static void m(String s) {
    s = "a";
    //@ check \old(s.length()) == 10;
    //@ check \old(s).length() == 10;
    //@ check s.length() == 1;
  }
  
  public static void main(String ... args) {
      m("abcdefghij");
      //+RAC@ set System.out.println("DONE");
  }
}
