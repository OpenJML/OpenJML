// @(#)$Id: JMLValueBagSpecs.java,v 1.16 2006/02/17 01:21:47 chalin Exp $

// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.


package org.jmlspecs.models;

/** Special behavior for JMLValueBag not shared by JMLObjectBag.
 *
 * @version $Revision: 1.16 $
 * @author Gary T. Leavens, with help from Clyde Ruby, and others.
 * @see JMLValueType
 * @see JMLValueBag
 */
//-@ immutable
public /*@ pure @*/ abstract class JMLValueBagSpecs implements JMLValueType {

    /** Is the argument ".equals" to one of the values in this bag.
     *  @see #has(Object)
     *  @see #count(JMLType)
     */
    /*@ public normal_behavior
      @   ensures \result <==> count(elem) > 0;
      @*/
    public abstract boolean has(/*@ nullable @*/ JMLType elem);

    /** Is the argument ".equals" to one of the values in this bag.
     *  @see #has(JMLType)
     *  @see #count(Object)
     */
    /*@   public normal_behavior
      @     requires elem != null;
      @     ensures \result
      @        <==> elem instanceof JMLType && has((JMLType)elem);
      @ also
      @   public normal_behavior
      @     requires elem == null;
      @     ensures \result == has(null);
      @*/    
    public boolean has(/*@ nullable @*/ Object elem) {
        if (elem == null) {
            return has(null);
        } else {
            return elem instanceof JMLType && has((JMLType)elem);
        }
    }  

    /** Tell many times the argument occurs ".equals" to one of the
     * values in this bag.
     *  @see #count(Object)
     *  @see #has(JMLType)
     */
    /*@ public normal_behavior
      @   ensures \result >= 0
      @       && (* \result is the number of times elem tests
      @              as ".equals" to one of the objects in the bag *);
      @*/
    public abstract int count(/*@ nullable @*/ JMLType elem);

    /** Tell many times the argument occurs ".equals" to one of the
     * values in this bag.
     *  @see #count(JMLType)
     *  @see #has(Object)
     */
    /*@   public normal_behavior
      @     requires elem != null;
      @     ensures \result
      @          == (elem instanceof JMLType ? count((JMLType)elem) : 0);
      @ also
      @   public normal_behavior
      @     requires elem == null;
      @     ensures \result == count(null);
      @*/    
    public int count(/*@ nullable @*/ Object elem) {
        if (elem == null) {
            return count(null);
        } else {
            return (elem instanceof JMLType ? count((JMLType)elem) : 0);
        }
    }  

    /** Tells the number of elements in the bag.
     */
    /*@ public normal_behavior
      @   ensures \result >= 0
      @        && (* \result is the number of elements in the bag *);
      @*/
    public abstract int int_size();

    // Specification inherited from JMLValueType.
    // Note: not requiring the \result contain "clones" of the elements of 
    // this, allows the implementer latitude to take advantage of the
    // nature of immutable types.
    public abstract Object clone();

    /** How many times does the argument occur as an objects
     *  representing values in the bag?
     *  @see #count(Object)
     */
    /*@ public normal_behavior
      @     ensures (* \result is the number of occurences of objects
      @                in this bag that are "==" to elem *);
      public model int countObject(JMLType elem); @*/

    /** Returns a new bag that contains all the elements of this and
     *  also the given argument.
     *  @see #insert(JMLType, int)
     */
    public abstract /*@ non_null @*/ JMLValueBag insert (/*@ nullable @*/ JMLType elem)
        /*@  public model_program {
          @    assume elem != null && int_size() < Integer.MAX_VALUE;
          @    JMLType copy = (JMLType) elem.clone();
          @    JMLValueBag returnVal = null;
          @   
          @    behavior
          @      assignable returnVal;
          @      ensures returnVal != null
          @           && (\forall JMLType e; !e.equals(copy);
          @                       countObject(e) == returnVal.countObject(e))
          @           && returnVal.countObject(copy) == 1
          @           && returnVal.int_size() == int_size() + 1;
          @
          @      return returnVal; 
          @  }
          @*/
        ;

    /** Returns a new bag that contains all the elements of this and
     *  also the given argument.
     *  @see #insert(JMLType)
     */
    /*@  public model_program {
      @    assume cnt >= 0;
      @    assume elem != null && int_size() < Integer.MAX_VALUE - cnt;
      @    JMLType copy = (JMLType) elem.clone();
      @    JMLValueBag returnVal = null;
      @   
      @    behavior
      @      assignable returnVal;
      @      ensures returnVal != null
      @           && (\forall JMLType e; e != copy;
      @                       countObject(e)
      @                        == returnVal.countObject(e))
      @           && returnVal.countObject(copy) == cnt
      @           && returnVal.int_size() == int_size() + cnt;
      @
      @      return returnVal; 
      @  }
      @
      @ also
      @    signals (IllegalArgumentException) cnt < 0;
      @*/
    public abstract /*@ non_null @*/ JMLValueBag insert (/*@ nullable @*/ JMLType elem,
                                                         int cnt)
        throws IllegalArgumentException;

}
