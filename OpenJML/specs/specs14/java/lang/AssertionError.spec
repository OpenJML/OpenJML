package java.lang;

// FIXME - what are the arguments of the contstructors for?
public class AssertionError extends java.lang.Error {

    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    /*@ pure */ public AssertionError();

    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    /*@ pure */ public AssertionError(java.lang.Object o);

    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    /*@ pure */ public AssertionError(boolean b);

    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    /*@ pure */ public AssertionError(char c);

    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    /*@ pure */ public AssertionError(int i);

    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    /*@ pure */ public AssertionError(long l);

    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    /*@ pure */ public AssertionError(float f);

    /*@ public normal_behavior
      @   ensures standardThrowable(null);
      @*/
    /*@ pure */ public AssertionError(double d);
}
