/*
 * This file is part of the OpenJML plugin project. 
 * Copyright 2006-2009 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.Date;

/**
 * A class that provides some (static) timing routines for performance
 * checking.
 */
public class Timer {
  
  /** The private value holding the time at the beginning of the timed 
   * period, that is, when markTime was called.
   */
  //@ non_null
  static private Date timer = new Date();
  
  /** Sets this timer to 0. */
  static public void markTime() {
    timer = new Date();
  }
  
  /** 
   * @return the number of seconds since the last call of markTime()
   */
  static public double getTime() {
    return (new Date().getTime() - timer.getTime())/1000.;
  }
  
  /** 
   * @return the number of seconds since the last call of markTime()
   * as a String enclosed in [ ]
   */
  static public String getTimeString() {
    return "[" + getTime() + "]";
  }

}
