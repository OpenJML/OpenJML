package java.lang;

// FIXME - needs completion
 
public class NumberFormatException extends IllegalArgumentException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public NumberFormatException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public NumberFormatException(String s);
}
