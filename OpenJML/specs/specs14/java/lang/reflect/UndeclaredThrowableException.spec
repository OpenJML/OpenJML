package java.lang.reflect;

// FIXME - neds completion
 
public class UndeclaredThrowableException extends RuntimeException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public UndeclaredThrowableException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public UndeclaredThrowableException(String s);
}
