package java.lang.reflect;

// FIXME - needs completion
 
public class InvocationTargetException extends Exception {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public InvocationTargetException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public InvocationTargetException(String s);
}
