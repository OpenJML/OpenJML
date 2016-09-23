// @(#)$Id: JMLObjectType.java,v 1.11 2005/12/23 17:02:06 chalin Exp $

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
                                                                              

/** Objects that are containers of object references.
 * It is the intention that classes that implement JMLObjectType be
 * "containers of objects", in the sense that the user is only
 * interested in the "object references", (addresses) themselves
 * as the elements in the container. (This is in opposition to 
 * the intention of classes that implement JMLValueType.) With
 * object containers, the object references are copied in operations
 * that create new instances of the container classes, e.g., clone().
 * So there is no "deep copy" made with classes that implement
 * JMLObjectType.
 *
 * @version $Revision: 1.11 $
 * @author Gary T. Leavens
 * @author Albert L. Baker
 * @see JMLType
 */
public interface JMLObjectType extends JMLType {

    /** Return a shallow copy of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof JMLObjectType;
      @*/
    public /*@ pure @*/ Object clone();    

    /** Tell whether this object is equal to the argument, using ==
     * for comparisons to compare contained objects.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result ==>
      @        ob2 != null
      @        && (* ob2 and this contain the same object references *);
      @*/
    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object ob2);
}
