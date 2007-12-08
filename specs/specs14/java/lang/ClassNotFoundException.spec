package java.lang;

// FIXME - complete this
 
public class ClassNotFoundException extends Exception {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public ClassNotFoundException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public ClassNotFoundException(String s);
}
