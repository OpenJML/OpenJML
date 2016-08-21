// @(#)$Id: JMLIterator.java,v 1.8 2005/07/08 10:03:57 davidcok Exp $

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

import java.util.Iterator;

/** A combination of JMLType and java.util.Iterator.
 *  None of these support the remove operation.
 * @version $Revision: 1.8 $
 * @author Gary T. Leavens
 * @see JMLEnumeration
 * @see JMLEnumerationToIterator
 */
public interface JMLIterator extends Iterator, JMLType {

    /** Return a clone of this iterator.
     */
    Object clone();

    /*@ also
      @   assignable \nothing;
      @*/
    /*@ pure @*/ boolean hasNext();

    //@ public instance represents moreElements <- hasNext();
}
