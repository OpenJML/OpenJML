package java.io;
 
public class ObjectStreamException extends IOException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public ObjectStreamException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public ObjectStreamException(String s);
}
