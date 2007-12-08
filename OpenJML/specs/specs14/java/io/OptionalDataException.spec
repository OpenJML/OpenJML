package java.io;

// FIXME - needs completion
 
public class OptionalDataException extends ObjectStreamException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public OptionalDataException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public OptionalDataException(String s);
}
