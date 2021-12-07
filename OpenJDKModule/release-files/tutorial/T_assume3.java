// openjml -esc -checkFeasibility=none T_assume3.java
public class T_assume3 {
  //@ requires i > 0;
  public void example(int i) {
    //@ assume i < 0;
    //@ assert false; // No error because the precondition and assume statement contradict!
  }
}
