package java.io;
 
public class UTFDataFormatException extends IOException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public UTFDataFormatException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public UTFDataFormatException(String s);
}
