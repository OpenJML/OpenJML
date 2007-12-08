package java.util;
 
public class ConcurrentModificationException extends RuntimeException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public ConcurrentModificationException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public ConcurrentModificationException(String s);
}
