package java.lang;
 
public class ArrayIndexOutOfBoundsException extends IndexOutOfBoundsException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public ArrayIndexOutOfBoundsException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null); // FIXME - what should this be
      @*/
    //@ pure
    public ArrayIndexOutOfBoundsException(int index);
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public ArrayIndexOutOfBoundsException(String s);
}
