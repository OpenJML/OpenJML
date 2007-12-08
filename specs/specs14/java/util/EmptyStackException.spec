package java.util;
 
public class EmptyStackException extends RuntimeException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public EmptyStackException();
  
}
