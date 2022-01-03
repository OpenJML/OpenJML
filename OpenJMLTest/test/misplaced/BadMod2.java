public class BadMod2 {

  public void m() {
    BadMod.m();
    //@ ghost int gg = BadMod.f;
  }
}
