package java.lang;
 
public class UnsupportedOperationException extends RuntimeException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public UnsupportedOperationException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public UnsupportedOperationException(String s);
}
