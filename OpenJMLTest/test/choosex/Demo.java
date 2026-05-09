public class Demo {

public static void main(String... args) {
  //@ ghost boolean b = \choosex int k; 0 < k < 10; k == 0;
  //@ assert !b; // OK
  m0(); m(); mm();
  //@ print "END";
}

//@ pure
public static void m0() {
  //@ ghost int i = \choose short k;;true;
  //@ assert i <= Short.MAX_VALUE;
}

//@ pure
public static void m() {
  //@ ghost boolean bb = \choosex short k;; k <= Short.MAX_VALUE;
  //@ assert bb; // OK
}

//@ pure
public static void mm() {
  //@ ghost boolean b2 = \choosex int k; 0 < k < 0; k == 0; // not well-defined
}

}
