package java.io;
 
abstract public class ObjectStreamException extends IOException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    protected ObjectStreamException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    protected ObjectStreamException(String s);
}
