public class RR {
  public void m() {
    var r = new R(10, true);
    //@ assert !r.bbbb();
    //@ assert r.x() == 100;
  }
}
