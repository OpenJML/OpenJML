// @(#)$Id: TotalCompareTo.java,v 1.10 2007/02/08 14:05:50 leavens Exp $

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

package org.jmlspecs.models.resolve;

/** Objects whose compareTo operation is guaranteed not to throw an
 *  {@link UndefinedException} and only throws a ClassCastException
 *  when the class of the argument prohibits comparison.
 *
 * @version $Revision: 1.10 $
 * @author Gary T. Leavens
 */
public interface TotalCompareTo extends ReflexiveCompareTo {

    /*@ also
      @   public behavior
      @     requires obj != null;
      @     ensures obj instanceof TotalCompareTo;
      @     signals_only ClassCastException;
      @     signals (ClassCastException)
      @             !(obj instanceof TotalCompareTo);
      @*/
    /*@ pure @*/ int compareTo(/*@ non_null @*/ Object obj)
        throws ClassCastException, NullPointerException;

    /*@ also
      @   public model_program {
      @     try {
      @       int r = this.compareTo(obj);
      @     } catch (ClassCastException e) {
      @       return false;
      @     }
      @     return true;
      @   }
      @*/
      //@ pure model boolean isComparableTo(Object obj);
}

