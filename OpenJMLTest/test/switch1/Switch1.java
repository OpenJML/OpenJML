// switch expression with colon
public class Switch1 {
  //@ ensures i == 1 ==> \result == 2;
  //@ ensures i == 3 ==> \result == 11;
  //@ ensures i == 4 ==> \result == 11;
  //@ ensures !(i==1||i==3||i==4) ==> \result == 20;
  static public int m(int i) {
    int j = switch (i) { case 1,1+2 : if (i==1) yield 2; case 4: { yield 11; } default: yield 20; };
    return j;
  }
  static public void main(String ... args) { System.out.println(m(args.length-2)); }
}
