package java.io;

// FIXME - needs completion
 
public class WriteAbortedException extends ObjectStreamException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public WriteAbortedException(String s);
}
