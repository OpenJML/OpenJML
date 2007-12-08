package java.net;
 
public class UnknownHostException extends java.io.IOException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public UnknownHostException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public UnknownHostException(String s);
}
