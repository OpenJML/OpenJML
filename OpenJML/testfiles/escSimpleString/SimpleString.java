/*
 * Fall 2013 CSCI181G - Homework 6
 * Static and Runtime Checking
 */

package esc;

/**
 * A trivial string class that supports initialization, 
 * concatenation and the substring operation.
 * 
 * @author Daniel M. Zimmerman
 * @author YOUR NAME HERE
 * @version 2013-11-04
 */
public class SimpleString {
  /*
   * The class should have a history constraint about the fact
   * that it is immutable ("final" on the array isn't quite good enough).
   */
  
  // Instance Fields
  
  /**
   * The character data of this SimpleString.
   */
  private /*@ spec_public */ final char[] my_chars;  
  
  // Constructors
  
  /**
   * Constructs a new SimpleString with the contents of the specified
   * array of characters in the order they appear in the array.
   * 
   * @param the_chars The array of characters.
   */
  //@ ensures (\forall int i; 0 <= i && i < my_chars.length; my_chars[i] == the_chars[i]);
  public SimpleString(final /*@ non_null */ char[] the_chars) {
    my_chars = new char[the_chars.length];
    // FIXME - these assumptions should be part of the logic encoding. Note that the first two seem to have to be after the assignment above
    //@ assume the_chars instanceof char[];
    //@ assume \elemtype(\typeof(my_chars)) == \type(char);
    //@ assume my_chars instanceof char[];
    System.arraycopy(the_chars, 0, my_chars, 0, the_chars.length);
  }

}
