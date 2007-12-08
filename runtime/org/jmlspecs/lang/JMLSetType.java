// @(#)$Id: JMLSetType.java,v 1.2 2005/12/23 17:02:06 chalin Exp $

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


package org.jmlspecs.lang;

// import java.util.Iterator;

/** Common protocol for the JML set model types.  This is put in
 * org.jmlspecs.lang because the language creates sets using set
 * comprehensions.  It should also be useful for the runtime assertion
 * checker and other tools, to know what it can count on from the JML
 * set types.
 *
 * @version $Revision: 1.2 $
 * @author Gary T. Leavens
 * @see org.jmlspecs.models.JMLCollection
 * @see org.jmlspecs.models.JMLEqualsSet
 * @see org.jmlspecs.models.JMLValueSet
 * @see org.jmlspecs.models.JMLObjectSet
 */
//-@ immutable
public /*@ pure @*/ interface JMLSetType
{
    //**************************** Observers **********************************

    /** Tell whether the argument is equal to one of the elements in
     * this collection, using the notion of element equality
     * appropriate for the collection.
     */
    /*@ public normal_behavior
      @     requires isEmpty();
      @     ensures ! \result ;
      @*/    
    boolean has(Object elem );

    // the equals method should be pure
    boolean equals(/*@ nullable @*/ Object s2);

    /** Is the set empty.
     * @see #int_size()
     * @see #has(Object)
     */
    /*@   public normal_behavior
      @     ensures \result == (\forall Object e; ; !this.has(e));
      @*/  
    boolean isEmpty();

    /** Tells the number of elements in the set.
     */
    /*@ public normal_behavior
      @    ensures this.isEmpty() ==> \result == 0;
      @    ensures \result >= 0;
      @*/
    int int_size( );

    /** Return an arbitrary element of this.
     *  @see #isEmpty()
     *  @see #elements()
     */
    /*@   public normal_behavior
      @      requires !isEmpty();
      @      ensures this.has(\result);
      @*/
    Object choose();

    // ****************** building new JMLSetTypes **************************

    /** Returns a new set that contains all the elements of this and
     *  also the given argument.
     *  @see #has(Object)
     *  @see #remove(Object)
     */
    /*@ 
      @  public normal_behavior
      @   requires int_size() < Integer.MAX_VALUE || has(elem);
      @   ensures \result != null
      @	  && (\forall Object e; ;
      @        \result.has(e) ==> this.has(e)
      @                            || (e == null && elem == null)
      @                            || (e != null && e.equals(elem)));
      @*/  
    /*@ non_null @*/ JMLSetType insert(Object elem);

    /** Return a new array containing all the elements of this.
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.length == int_size()
      @         && (\forall Object o; has(o);
      @              (\exists int i;
      @                   (o == null && \result[i] == null)
      @                || (o != null && o.equals(\result[i]))));
      @*/
    /*@ non_null @*/ Object[] toArray();

// we could include the following if we were willing to put the type
// JMLIterator into org.jmlspecs.lang also
//    /** Returns an Iterator over this set.
//     */
//    /*@  public normal_behavior
//      @      ensures \fresh(\result)
//      @          && \result.equals(new JMLEnumerationToIterator(elements()));
//      @*/  
//    JMLIterator iterator();

}
