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

package org.jmlspecs.genericmodels;

import org.jmlspecs.annotation.*;

/** JMLTypes with an compareTo operation, as in {@link java.lang.Comparable}.
 *
 * @author Gary T. Leavens, generics by DRCok
 * @see java.lang.Comparable
 */
//+OPENJML@ immutable
public @Pure interface JMLComparable<T>
    extends JMLType, Comparable<T> {

    /** Compare this to o, returning a comparison code.
     *  @param o the object this is compared to.
     *  @exception ClassCastException when o doesn't have an appropriate type.
     */
    /*@ also
      @   public behavior
      @     requires o != null;
      @     ensures (* o is an instance of a comparable class *);
      @     ensures (* if this is equal to o, then \result is 0 *)
      @         && (* if this is less than o, then \result is negative *)
      @         && (* if this is greater than o, then \result is positive *);
      @     signals_only ClassCastException;
      @     signals (ClassCastException)
      @          (* o is not an instance of a comparable class *);
      @*/
    public int compareTo(@NonNull T o) throws ClassCastException;

}

