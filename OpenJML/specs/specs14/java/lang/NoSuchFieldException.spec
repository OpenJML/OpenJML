package java.lang;
 
public class NoSuchFieldException extends Exception {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public NoSuchFieldException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public NoSuchFieldException(String s);
}
