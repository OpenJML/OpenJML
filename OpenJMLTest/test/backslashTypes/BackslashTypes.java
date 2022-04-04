public class BackslashTypes<T> {

  public void m() {
    //@ ghost seq<T> snb = seq.<T>empty();
    //@ ghost \seq<T> s = \seq.<T>empty();
    //@ assert s.size() == 0;
  }
}
