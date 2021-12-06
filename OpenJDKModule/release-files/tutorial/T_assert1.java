// openjml -esc T_assert1.java

public class T_assert1 {

  public void example(int i) {
    int neg;
    if (i > 0) {
      neg = -i;
    } else {
      neg = i;
    }
    //@ assert neg <= 0;
  }
}
