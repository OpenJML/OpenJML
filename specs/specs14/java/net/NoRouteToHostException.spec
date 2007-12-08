package java.net;
 
public class NoRouteToHostException extends SocketException {
  
    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    //@ pure
    public NoRouteToHostException();
  
    /*@ public normal_behavior
      @   ensures standardThrowable(s);
      @*/
    //@ pure
    public NoRouteToHostException(String s);
}
