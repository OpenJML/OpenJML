public class LC {

  public static void main(String ... args) {
    int i = 0;
    //@ loop_invariant \count == 0 ? i == 0 : (0 <= i <= 10);
    do {
     ++i;
    } while (i < 10);
    //@ assert i == 10;

  }
}
