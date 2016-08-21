// @(#)$Id: JMLEnumeration.java,v 1.7 2005/07/07 21:03:06 leavens Exp $

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

import java.util.Enumeration;

/** A combination of JMLType and java.util.Enumeration.
 * @version $Revision: 1.7 $
 * @author Gary T. Leavens
 * @see JMLIterator
 * @see JMLEnumerationToIterator
 */
//-@ immutable
public interface JMLEnumeration extends Enumeration, JMLType {

    /** Return a clone of this enumeration.
     */
    Object clone();

    /*@ also
      @   assignable \nothing;
      @*/
    /*@ pure @*/ boolean hasMoreElements();

    //@ public instance represents moreElements <- hasMoreElements();
}
