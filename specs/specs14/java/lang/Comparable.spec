// @(#)$Id: Comparable.spec 2240 2006-12-16 17:12:00Z chalin $

// Copyright (C) 2001-2006 Iowa State University, DSRG.org.

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.lang;

/** JML's specification of java.lang.Comparable.
 * These are objects with a total ordering that is an equivalence relation.
 * @version $Revision: 2240 $
 * @author Gary T. Leavens, et al.
 */
public interface Comparable {

    /*@   public normal_behavior
      @     requires i < 0;
      @     ensures \result == -1;
      @ also
      @   public normal_behavior
      @     requires i == 0;
      @     ensures \result == 0;
      @ also
      @   public normal_behavior
      @     requires i > 0;
      @     ensures \result == 1;
      @ implies_that
      @   public model_program {
      @     return ((i < 0) ? -1 : ((i == 0) ? 0 : 1));
      @   }
      @ model static pure int sgn(int i);
      @*/

    /*@ public normal_behavior
      @   requires !(\typeof(o) <: \type(Comparable));
      @   ensures  !\result;
      @ also public normal_behavior
      @   requires \typeof(o) <: \type(Comparable);
      @    ensures ((\typeof(this) <: \typeof(o)) ||
      @			(\typeof(o) <: \typeof(this))) ==> \result;
      @ // subclasses will strengthen this contract.
      @ public model pure boolean
      @ definedComparison(non_null Object o);
      @*/

    /*@ public exceptional_behavior
      @    requires !definedComparison(o);
      @    signals_only ClassCastException;
      @ also public normal_behavior
      @    requires definedComparison(o);
      @    ensures o == this ==> \result == 0; // reflexive
      @    ensures sgn(\result) == - sgn(((Comparable)o).compareTo(this)); // antisymmetric
      @*/
    /*@ pure @*/ int compareTo(/*@ non_null */ Object o);

    // compareTo is reflexive
    /*+@ public instance invariant
      @   (\forall Comparable x; x != null; x.compareTo(x) == 0);
      @*/
}
