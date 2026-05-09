public class LBL {

  public static void main(String... args) {
    //@ ghost int x = 10;
    //@ ghost int y = 20;
    //@ ghost int z = 30 - (\lbl A x+y);
    //@ ghost int w = 30 - \lbl(B, x+y);
    //@ assert z != w;
  }
}
