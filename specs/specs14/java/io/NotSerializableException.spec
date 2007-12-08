package java.io;
 
public class NotSerializableException extends ObjectStreamException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public NotSerializableException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public NotSerializableException(String s);
}
