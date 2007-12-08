package java.lang;
 
public class IllegalMonitorStateException extends RuntimeException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public IllegalMonitorStateException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public IllegalMonitorStateException(String s);
}
