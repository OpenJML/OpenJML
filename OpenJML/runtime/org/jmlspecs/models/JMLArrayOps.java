// @(#)$Id: JMLArrayOps.java,v 1.12 2005/07/07 21:03:06 leavens Exp $

// Adapted in part from Compaq SRC's specification for ESC/Java

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

/** Array Operations that are useful for specifications.
 *
 * @version $Revision: 1.12 $
 * @author Brandon Shilling
 * @author Gary T. Leavens
 * @see java.util.Arrays
 * @see JMLObjectSequence
 * @see JMLValueSequence
 */
public class JMLArrayOps {

    /** Search the array for the given element and return how many
     *  times that element's object identity occurs in the array.
     *  @see #objectIdentityCount(Object[], Object, int)
     *  @see #hasObjectIdentity(Object[], Object)
     *  @see #valueEqualsCount(Object[], Object)
     */
    /*@ public normal_behavior
      @    requires array != null;
      @    ensures \result == (\num_of int i; 0 <= i && i < array.length;
      @                                       array[i] == element);
      @*/
    public static /*@ pure @*/ int objectIdentityCount(
        /*@ non_null @*/ Object[] array,
        Object element)
    {
        return objectIdentityCount( array, element, array.length );
    }

    /** Search the array for the given element and return how many
     *  times that element's object identity occurs in the array from
     *  0 the given length-1.
     *  @see #objectIdentityCount(Object[], Object)
     *  @see #hasObjectIdentity(Object[], Object, int)
     *  @see #valueEqualsCount(Object[], Object, int)
     */
    /*@ public normal_behavior
      @    requires array != null;
      @    requires 0 <= length && length <= array.length;
      @    ensures \result == (\num_of int i; 0 <= i && i < length;
      @                                       array[i] == element);
      @ implies_that
      @     requires 0 <= length && length <= array.length;
      @*/
    public static /*@ pure @*/ int objectIdentityCount(
        /*@ non_null @*/ Object[] array,
        Object element, 
        int length)
    {
        int elementCount=0; 
    	for (int i=0; i<length; i++) {
            if (element==array[i]) {
                elementCount++; 
            }
        }
	return elementCount; 
    }  

    /** Search the array for the given element and return how many
     *  times an object with value "equals" to the given element occurs
     *  in the array.
     *  @see #valueEqualsCount(Object[], Object, int)
     *  @see #hasValueEquals(Object[], Object)
     *  @see #objectIdentityCount(Object[], Object)
     */
    /*@ public normal_behavior
      @    requires array != null;
      @    ensures \result
      @             == (\num_of int i; 0 <= i && i < array.length;
      @                       (array[i] == null ==> element == null)
      @                    && (array[i] != null
      @                        ==> (* array[i].equals(element) *) ));
      @*/
    public static /*@ pure @*/ int valueEqualsCount(
        /*@ non_null @*/ Object[] array,
        Object element)
    {
        return valueEqualsCount( array, element, array.length );
    }

    /** Search the array for the given element and return how many
     *  times an object with value "equals" to the given element occurs
     *  in the array from 0 the given length-1.
     *  @see #valueEqualsCount(Object[], Object)
     *  @see #hasValueEquals(Object[], Object, int)
     *  @see #objectIdentityCount(Object[], Object, int)
     */
    /*@ public normal_behavior
      @    requires array != null;
      @    requires 0 <= length && length <= array.length;
      @    ensures \result
      @             == (\num_of int i; 0 <= i && i < length;
      @                       (array[i] == null ==> element == null)
      @                    && (array[i] != null
      @                        ==> (* array[i].equals(element) *) ));
      @ implies_that
      @    requires 0 <= length && length <= array.length;
      @*/
    public static /*@ pure @*/ int valueEqualsCount(
        /*@ non_null @*/ Object[] array,
        Object element, 
        int length)
    {
        int valueEqCount=0; 
    	for (int i=0; i<length; i++) {
            if (element == null) {
                if (array[i] == null) {
                    valueEqCount++;
                }
            } else if (element.equals(array[i])) {
	      valueEqCount++; 
            }
        }
	return valueEqCount; 
    }  


    /** Search the array for the given element and tell if
     *  that element's object identity occurs in the array.
     *  @see #hasObjectIdentity(Object[], Object, int)
     *  @see #objectIdentityCount(Object[], Object)
     *  @see #hasValueEquals(Object[], Object)
     */
    /*@ public normal_behavior
      @    requires array != null;
      @    ensures \result == (\exists int i; 0 <= i && i < array.length;
      @                                       array[i] == element);
      @*/
    public static /*@ pure @*/ boolean hasObjectIdentity(
        /*@ non_null @*/ Object[] array,
        Object element)
    {
        return hasObjectIdentity( array, element, array.length );
    }

    /** Search the array for the given element and tell if that
     * element's object identity occurs in the array from 0 the given
     * length-1.
     *  @see #hasObjectIdentity(Object[], Object)
     *  @see #objectIdentityCount(Object[], Object)
     *  @see #hasValueEquals(Object[], Object)
     */
    /*@ public normal_behavior
      @    requires array != null;
      @    requires 0 <= length && length <= array.length;
      @    ensures \result == (\exists int i; 0 <= i && i < length;
      @                                       array[i] == element);
      @ implies_that
      @    requires 0 <= length && length <= array.length;
      @*/
    public static /*@ pure @*/ boolean hasObjectIdentity(
        /*@ non_null @*/ Object[] array,
        Object element, 
        int length)
    {
    	for (int i=0; i<length; i++) {
            if (element==array[i]) {
                return true;
            }
        }
	return false;
    }  

    /** Search the array for the given element and tell if an object
     *  with value "equals" to the given element occurs in the array.
     *  @see #hasValueEquals(Object[], Object, int)
     *  @see #valueEqualsCount(Object[], Object)
     *  @see #hasObjectIdentity(Object[], Object)
     */
    /*@ public normal_behavior
      @    requires array != null;
      @    ensures \result
      @             == (\exists int i; 0 <= i && i < array.length;
      @                       (array[i] == null ==> element == null)
      @                    && (array[i] != null
      @                        ==> (* array[i].equals(element) *) ));
      @*/
    public static /*@ pure @*/ boolean hasValueEquals(
        /*@ non_null @*/ Object[] array,
        Object element)
    {
        return hasValueEquals( array, element, array.length );
    }

    /** Search the array for the given element and tell if an object
     *  with value "equals" to the given element occurs in the array
     *  from 0 the given length-1.
     *  @see #hasValueEquals(Object[], Object)
     *  @see #valueEqualsCount(Object[], Object, int)
     *  @see #hasObjectIdentity(Object[], Object, int)
     */
    /*@ public normal_behavior
      @    requires array != null;
      @    requires 0 <= length && length <= array.length;
      @    ensures \result
      @             == (\exists int i; 0 <= i && i < length;
      @                       (array[i] == null ==> element == null)
      @                    && (array[i] != null
      @                        ==> (* array[i].equals(element) *) ));
      @ implies_that
      @    requires 0 <= length && length <= array.length;
      @*/
    public static /*@ pure @*/ boolean hasValueEquals(
        /*@ non_null @*/ Object[] array,
        Object element, 
        int length)
    {
    	for (int i=0; i<length; i++) {
            if (element == null) {
                if (array[i] == null) {
                    return true;
                }
            } else if (element.equals(array[i])) {
               return true;
            }
        }
	return false;
    }  

}
