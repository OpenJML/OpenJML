// @(#)$Id: JMLCollection.java,v 1.13 2006/12/02 23:38:15 leavens Exp $

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

/** Common protocol of the JML model collection types.
 *
 * The use of elementType and containsNull in this specification
 * follows the ESC/Java specification of {@link java.util.Collection}.
 * That is, these ghost fields are used by the user of the object to
 * state what types of objects are allowed to be added to the collection,
 * and hence what is guaranteed to be retrieved from the collection.  They
 * are not adjusted by methods based on the content of the collection.
 *
 * @version $Revision: 1.13 $
 * @author Gary T. Leavens
 * @author Yoonsik Cheon
 * @see JMLEnumeration
 * @see JMLIterator
 */
//-@ immutable
public interface JMLCollection extends JMLType {

    /** The objectState of all elements is contained in elementState. */
    //@ public model instance JMLDataGroup elementState;

    /** The type of the elements in this collection.
     */
    //@ instance
    //@    ghost public \TYPE elementType;

    //@ public instance constraint elementType == \old(elementType);

    /** Whether this collection can contain null elements;
     *  think of it as "is allowed to contain null".
     */
    //@ instance
    //@    ghost public boolean containsNull;

    //@ public instance constraint containsNull == \old(containsNull);


    /** Returns an Iterator over this object.
     */
    //@ public normal_behavior
    //@    ensures \fresh(\result) && \result.elementType == this.elementType;
    //@    ensures !containsNull ==> !\result.returnsNull;
    /*@ pure @*/ /*@ non_null @*/ JMLIterator iterator();

    /** Tell whether the argument is equal to one of the elements in
     * this collection, using the notion of element equality
     * appropriate for the collection.
     */
    /*@ public normal_behavior
      @    ensures (* \result <==> elem is equal to one of the elements
      @                            in the collection. *);
      @    ensures_redundantly !containsNull && elem == null ==> !\result;
      @    ensures_redundantly 
      @       elem != null && !(\typeof(elem) <: elementType) ==> !\result;
      @*/    
    /*@ pure @*/ boolean has(/*@ nullable @*/ Object elem);

    // !FIXME! put in containsAll and containsAll, and
    // look for other common methods.

    /** Tell the number of elements in this collection.
     */
    /*@ public normal_behavior
      @    ensures \result >= 0
      @         && (* \result is the size of this collection *);
      @*/
    //@ model pure public \bigint size( );

    /*@ public normal_behavior
      @    requires size() <= Integer.MAX_VALUE;
      @    ensures \result == size();
      @*/
    /*@ pure @*/ public int int_size( );

}
