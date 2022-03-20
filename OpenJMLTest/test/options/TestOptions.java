public class TestOptions {

  public void n() {
    //@ assert false;
  }

  @org.jmlspecs.annotation.Options({"-timeout=10","-progress"})
  public void m() {
    //@ assert false;
  }

}
