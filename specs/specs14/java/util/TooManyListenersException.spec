package java.util;
 
public class TooManyListenersException extends Exception {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public TooManyListenersException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public TooManyListenersException(String s);
}
