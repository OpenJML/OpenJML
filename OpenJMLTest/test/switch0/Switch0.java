// switch statement with ->
public class Switch0 {

  //@ ensures i == 1 ==> \result == 4;
  //@ ensures i == 2 ==> \result == 6;
  //@ ensures (i != 1 && i != 2) ==> \result == 0;
  public static int m(int i) {
    int k = 0;
    switch (i) { case 1 -> k=4; case 2 -> { k = 6;} }
    return k;
  }

  public static void main(String ... args) { System.out.println(m(1) + " " + m(2) + " " + m(3)); }
}
