// openjml -esc T_assert3.java

public class T_assert3 {

  public void example(int i) {
    int neg;
    if (i > 0) {
      neg = -i;
    } else {
      neg = i;
    }
    assert neg < 0; // A Java assert statement (but interpreted by JML)
  }
}
