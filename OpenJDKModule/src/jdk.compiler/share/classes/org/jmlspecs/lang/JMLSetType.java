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

import org.jmlspecs.annotation.*;

/** Common protocol for the JML set model types.  This is put in
 * org.jmlspecs.lang because the language creates sets using set
 * comprehensions.  It should also be useful for the runtime assertion
 * checker and other tools, to know what it can count on from the JML
 * set types.
 *
 * @version $Revision: 1.2 $
 * @author Gary T. Leavens, David R. Cok
 * @see org.jmlspecs.models.JMLCollection
 * @see org.jmlspecs.models.JMLEqualsSet
 * @see org.jmlspecs.models.JMLValueSet
 * @see org.jmlspecs.models.JMLObjectSet
 */
//+OPENJML@ immutable
public @Pure interface JMLSetType<E> extends JMLIterable<E>
{
    
    //**************************** Observers **********************************

    /** Tell whether the argument is equal to one of the elements in
     * this collection, using the notion of element equality
     * appropriate for the collection.
     * 
     * This method defines the model of what is or is not in the set.
     */
    /*@ public normal_behavior
      @     ensures isEmpty() ==> !\result;
      @     //ensures !(elem instanceof E) ==> !\result; // illegal Java TODO
      @*/    
    boolean has(@Nullable Object elem );  // TODO - should be contains?

    //@ public normal_behavior
    //@    ensures s2 == null ==> !\result;
    //@    ensures !(s2 instanceof JMLSetType) ==> !\result; // TODO should be JMLSetType<E>
    boolean equals(@Nullable Object s2);
    
    //@ public normal_behavior
    //@   ensures (item == o) ==> (\result == true);
    //@   ensures ((item == null) != (o == null)) ==> (\result == false);
    boolean elem_equals(@Nullable E item, @Nullable Object o);

    // This invariant ties the definition of has to that of elem_equals and
    // imposes 'setness' on this object - no duplicate objects (measured by elem_equals)
    // Note that changes to the contents of objects in a set may change which elements
    // are equal to others and therefore whether this invariant remains true.
    //@ public invariant (\forall E e1, e2; elem_equals(e1,e2) ==> (has(e1) <==> has(e2)));

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
     */
    /*@   public normal_behavior
      @      requires !isEmpty();
      @      ensures this.has(\result);
      @*/
    @Nullable E choose();

    // ****************** building new JMLSetTypes **************************

    /** Returns a new set that contains all the elements of this and
     *  also the given argument.
     *  @see #has(Object)
     */
    /*@ 
      @  public normal_behavior
      @   requires int_size() < Integer.MAX_VALUE || has(elem);
      @   ensures (\forall Object e; \result.has(e);
      @                  (this.has(e) || elem_equals(e,elem)));
      @   ensures (\forall Object e; this.has(e); \result.has(e));
      @   ensures  this.has(elem) ==> (this.int_size() == \result.int_size());
      @   ensures  !this.has(elem) ==> (this.int_size()+1 == \result.int_size());
      @*/
    @NonNull JMLSetType<E> insert(@Nullable E elem);

    /** Return a new array containing all the elements of this.
     */
    /*@ public normal_behavior
      @    ensures \result != null;
      @    ensures \result.length == this.int_size();
      @    ensures (\forall Object o; has(o);
      @              (\exists int i;
      @                   elem_equals(o,\result[i])));
      @*/
    E[] toArray(); // CAUTION - be careful of JSR308 syntax // FIXME - should be @Readonly 

    /** Returns an Iterator over this set.
     */
    /*@  public normal_behavior
      @      ensures \fresh(\result);
      @*/  
    @NonNull JMLIterator<E> iterator();

}
