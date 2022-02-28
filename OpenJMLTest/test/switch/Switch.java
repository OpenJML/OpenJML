// Switch expression with ->
public class Switch {

  //@ ensures (i == 1 || i == 3) ==> \result == 12;
  //@ ensures i == 2 ==> \result == 23;
  //@ ensures (i <=0 || i >=5) ==> \result == 44;
  //@ signals (IllegalArgumentException e) i == 4;
  public static int m(int i) {
    int j = 1;
    j = j + switch (i) { case 1,3 -> 11; case 2 -> { int k = 20; yield k+i; } case 4 -> throw new IllegalArgumentException(); default -> 33+10; };
    //@ show i,j;
    return j;
  }

  public static void main(String ... args) {
    System.out.println(m(1) + " " + m(2) + " " + m(3) + " " + m(0));
  }
}
