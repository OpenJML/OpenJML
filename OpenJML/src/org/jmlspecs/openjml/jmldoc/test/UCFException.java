package org.jmlspecs.openjml.jmldoc.test;

public class UCFException extends Exception {

  //@ invariant true;
  //@ constraint false;
  //@ initially true;
  //@ axiom true;
    
  //@ ensures \result == true;
   public /*@ pure */ boolean hasInternet() {
       return true;
   }
   
}
