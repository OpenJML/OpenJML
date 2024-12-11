public class TestOptions {

  public void n() {
    //@ assert false;
  }

  @org.jmlspecs.annotation.Options({"-timeout=1","-progress"})  // Intentional timeout (some of the time)
  public void m() {
    //@ assert false;
  }

}
