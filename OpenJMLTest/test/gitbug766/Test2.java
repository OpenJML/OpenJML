public class Test2 {

  /*@ ensures (\exists boolean x1; x1 == \result; \exists boolean z1; z1 == true; x1 == z1)
              ==>
              (\exists int x2; x2 == number; \exists int z2; (z2 == 0); x2 == z2);
  @*/
  /* @ensures (\exists boolean x1; x1 == \result; \exists boolean z1; z1 == false; x1 == z1)
              ==>
              (\exists int x2; x2 == number; \exists int z2; !(z2 == 0); x2 == z2);
  @*/
  public boolean m(int number) { return number == 0; }
}
