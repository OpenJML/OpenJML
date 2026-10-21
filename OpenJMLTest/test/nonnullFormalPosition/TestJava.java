// The implicit non-null conjunct of a callee precondition is reported at the formal in the
// callee spec file (B.jml), not at an offset taken from the caller
public class TestJava {
  public void m() {
    B.f(1, null);
  }
}
