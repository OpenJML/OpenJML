// @(#)$Id: CompareTo.java,v 1.13 2007/02/08 14:05:50 leavens Exp $

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

/** Objects with a compareTo operation.  Unlike {@link
 * java.lang.Comparable}, this operation is not assumed to be a total
 * order, and may be partial.
 *
 * @version $Revision: 1.13 $
 * @author Gary T. Leavens
 * @see TotallyOrderedCompareTo
 */
public interface CompareTo {

    /** Compare this to obj, returning negative if this is
     *  strictly less than obj, 0 if they are equal, and
     *  positive otherwise.
     */
    /*@ public behavior
      @  requires obj != null;
      @  ensures isComparableTo(obj);
      @  ensures (* returns if this is comparable to obj *);
      @  signals_only UndefinedException, ClassCastException;
      @  signals (UndefinedException e)
      @         (* no comparison between this and obj is defined *)
      @         && e != null;
      @  signals (ClassCastException e)
      @         (* obj's type prevents it from being compared to this *)
      @         && e != null;
      @*/
    /*@ pure @*/ int compareTo(/*@ non_null @*/ Object obj)
        throws UndefinedException, ClassCastException, NullPointerException;

    /** Tells whether this has a defined comparision with obj.
     */
    /*@
      @ public normal_behavior
      @     ensures \result <==>
      @          (* there is a defined comparison between obj and this *);
      @ also
      @   public model_program {
      @     try {
      @       int r = this.compareTo(obj);
      @     } catch (UndefinedException e) {
      @       return false;
      @     } catch (ClassCastException e) {
      @       return false;
      @     }
      @     return true;
      @   }
      pure model boolean isComparableTo(non_null Object obj);
      @*/
}
