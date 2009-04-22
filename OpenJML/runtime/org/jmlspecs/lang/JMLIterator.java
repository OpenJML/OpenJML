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

import org.jmlspecs.annotations.*;


/** A combination of JMLType and java.util.Iterator.
 *  None of these support the remove operation.
 * @version $Revision: 1.8 $
 * @author Gary T. Leavens
 * @see JMLEnumeration
 * @see JMLEnumerationToIterator
 */

// FIXME - the design of immutable iterators is not finalized
@Pure
public interface JMLIterator<E> {

    /** Return a clone of this iterator.
     */
    Object clone();
    
    //@ also public normal_behavior
    /*@ ensures (o == null || !(o instanceof JMLIterator<E>)) ==> !\result;
      @ ensures (o != null && (o instanceof JMLIterator<E>) &&
             hasNext() != ((JMLIterator<E>)o).hasNext()) ==> !\result;
      @ ensures (o != null && (o instanceof JMLIterator<E>) &&
             !hasNext() && !((JMLIterator<E>)o).hasNext()) ==> \result;
      @ ensures (o != null && (o instanceof JMLIterator<E>) &&
             !advance().equals((JMLIterator<E>)o).advance()) ==> !\result;
      @*/
    boolean equals(Object o);

    /** Returns true if there is a next element */
    //@ public normal_behavior
    //@   ensures true;
    boolean hasNext();
    
    /** Returns an iterator for the tail of the sequence (since JMLIterators
     * are immutable).
     * @return an iterator for the tail of the sequence
     */
    //@ public normal_behavior
    //@ requires hasNext();
    @NonNull JMLIterator<E> advance();
    
    //@ public normal_behavior
    //@ requires hasNext();
    E value();

    //@ public instance represents moreElements <- hasNext();
}
