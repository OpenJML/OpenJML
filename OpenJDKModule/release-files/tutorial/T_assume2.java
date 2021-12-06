// openjml -esc T_assume2.java
public class T_assume2 {
  //@ requires i > 0;
  public void example(int i) {
    //@ assert false; // Blatant verification failure
  }
}
