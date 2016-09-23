// @(#)$Id: JMLNoSuchElementException.java,v 1.7 2005/07/07 21:03:07 leavens Exp $

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

import java.util.NoSuchElementException;

/** Missing element exception used by various JML collection types and
 * enumerators.
 *
 * @version $Revision: 1.7 $
 * @author Gary T. Leavens
 */
//-@ immutable
//@ pure
public class JMLNoSuchElementException extends NoSuchElementException {

    /** Initialize this object.
     */
    public JMLNoSuchElementException() {
        super();
    }

    /** Initialize this object with the given detail string.
     */
    public JMLNoSuchElementException(String s) {
        super(s);
    }
}
