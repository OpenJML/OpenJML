// gitbug766 with the range and body of the inner \exists exchanged, so RAC has a bound for z2
public class Test {

  /*@ ensures (\exists boolean x1; x1 == \result; \exists boolean z1; z1 == true; x1 == z1)
              ==>
              (\exists int x2; x2 == number; \exists int z2; x2 == z2; (z2 % 2 == 0));
  @*/
  /*@ ensures (\exists boolean x1; x1 == \result; \exists boolean z1; z1 == false; x1 == z1)
              ==>
              (\exists int x2; x2 == number; \exists int z2; x2 == z2; !(z2 % 2 == 0));
  @*/
  public boolean m(int number) { return number%2 == 0; }

  //@ skipesc // only drives the RAC test
  public static void main(String[] args) {
    Test t = new Test();
    Test2 t2 = new Test2();
    for (int i = -3; i <= 3; i++) System.out.println(i + " " + t.m(i) + " " + t2.m(i));
  }
}
