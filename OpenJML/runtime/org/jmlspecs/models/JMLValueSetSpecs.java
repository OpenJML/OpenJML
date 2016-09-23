// @(#)$Id: JMLValueSetSpecs.java,v 1.17 2006/02/17 01:21:47 chalin Exp $

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

/** Special behavior for JMLValueSet not shared by JMLObjectSet.
 *
 * @version $Revision: 1.17 $
 * @author Gary T. Leavens, with help from Clyde Ruby, and others.
 * @see JMLValueType
 * @see JMLValueSet
 */
//-@ immutable
public /*@ pure @*/ abstract class JMLValueSetSpecs implements JMLValueType {

    /** Is the argument ".equals" to one of the values in the set.
     *  @see #has(Object)
     */
    /*@ public normal_behavior
      @   ensures \result <==>
      @         (* elem tests as ".equals" to one of the objects in the set *);
      @*/
    public abstract boolean has(/*@ nullable @*/ JMLType elem);

    /** Is the argument ".equals" to one of the values in theSet.
     *  @see #has(JMLType)
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
    public boolean has(/*@ nullable @*/ Object elem ) {
        if (elem == null) {
            return has(null);
        } else {
            return elem instanceof JMLType && has((JMLType)elem);
        }
    }  

    /** Tells the number of elements in the set.
     */
    //@ public normal_behavior
    /*@   ensures \result >= 0
      @        && (* \result is the number of elements in the set *);
      @*/
    public abstract int int_size(); 

    // Specification inherited from JMLValueType.
    // Note: not requiring the \result contain "clones" of the elements of 
    // this, allows the implementer latitude to take advantage of the
    // nature of immutable types.
    public abstract Object clone();

    /** Is the argument one of the objects representing values in the set?
     *  @see #has(Object)
     */
    /*@ public normal_behavior
      @     ensures \result <==>
      @            (* elem tests as "==" to one of the objects in the set *);
      public model boolean hasObject(JMLType elem); @*/

    /** Returns a new set that contains all the elements of this and
     *  also the given argument.
     */
    public abstract /*@ non_null @*/ JMLValueSet insert (/*@ nullable @*/ JMLType elem)
        /*@  public model_program {
          @    choose_if
          @      {
          @        assume has(elem) && (this instanceof JMLValueSet);
          @        return (JMLValueSet) this; 
          @      }
          @    or
          @      {
          @        assume elem == null && !has(null);
          @        assume int_size() < Integer.MAX_VALUE;
          @        JMLValueSet returnVal = null;
          @        behavior
          @          assignable returnVal;
          @          ensures returnVal != null
          @            && (\forall JMLType e; hasObject(e);
          @                                   returnVal.hasObject(e))
          @            && returnVal.has(null)
          @            && returnVal.int_size() == int_size() + 1;
          @        return returnVal; 
          @      } 
          @    or
          @      {
          @        assume !has(elem) && elem != null;
          @        assume int_size() < Integer.MAX_VALUE;
          @        JMLType copy = (JMLType) elem.clone();
          @        JMLValueSet returnVal = null;
          @        behavior
          @          assignable returnVal;
          @          ensures returnVal != null
          @            && (\forall JMLType e; hasObject(e);
          @                                   returnVal.hasObject(e))
          @            && returnVal.hasObject(copy)
          @            && returnVal.int_size() == int_size() + 1;
          @        return returnVal; 
          @      } 
          @  }
          @*/
        ;

}
