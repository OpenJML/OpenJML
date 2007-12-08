package java.io;
// FIXME - neeeds completion
 
public class InvalidClassException extends ObjectStreamException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public InvalidClassException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public InvalidClassException(String s);
}
