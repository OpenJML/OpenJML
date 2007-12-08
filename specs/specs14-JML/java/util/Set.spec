// @(#)$Id: Set.spec,v 1.25 2006/12/11 21:16:18 chalin Exp $

// Adapted in part from Compaq SRC's specification for ESC/Java

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

package java.util;

//+@ model import org.jmlspecs.models.*;

/** JML's specification of java.util.Set.
 * @version $Revision: 1.25 $
 * @author Brandon Shilling
 * @author Gary T. Leavens
 */
public interface Set extends Collection {

    /*+@ public model instance non_null JMLEqualsSet theSet;
      @                                               in theCollection;
      @ public instance represents theCollection <- theSet.toBag();
      @*/

    // specification inherited
    //@ pure
    int size();

    // specification inherited
    //@ pure
    boolean isEmpty();

    // specification inherited
    //@ pure
    boolean contains(/*@nullable*/ Object o);

    // specification inherited
    //@ pure
    Iterator iterator();

    // specification inherited
    //@ pure
    Object[] toArray();

    // specification inherited
    Object[] toArray(Object[] a);

    /*+@ also
       @ public behavior
       @   assignable theCollection;
       @   ensures \result <==> !\old(theSet.has(o));
       @   ensures theSet.equals(\old(theSet.insert(o)));
       @*/
    /*-@ also
       @ public normal_behavior
       @   requires contains(o);
       @   assignable \nothing;
       @   ensures !\result;
       @   ensures (\forall Object o; contains(o) <==> \old(contains(o)));
       @   ensures contains(null) <==> \old(contains(null));
       @ also public normal_behavior
       @   requires !contains(o);
       @   assignable _theCollection;
       @   ensures \result;
       @   ensures contains(o);
       @   ensures contains(null) <==> (\old(contains(null)) || o==null);
       @   ensures (\forall Object oo; contains(oo) <==> 
                                (\old(contains(oo)) || o == oo));
       @   ensures size() == \old(size()) + 1;
       @   ensures equal(_theCollection,0,\old(_theCollection),0,
                                   \old(_theCollection.length));
       @   ensures _theCollection[_theCollection.length-1] == o;
       @*/
    boolean add(/*@nullable*/ Object o);

    /*+@ also
       @ implies_that
       @ public behavior
       @   assignable theCollection;
       @   assignable_redundantly theSet;
       @   ensures !theSet.has(o);
       @   ensures_redundantly !theCollection.has(o);
       @*/
    /*-@ also
       @ public normal_behavior
       @   requires !contains(o);
       @   assignable \nothing;
       @   ensures \result;
       @   ensures (\forall Object o; contains(o) <==> \old(contains(o)));
       @   ensures contains(null) <==> \old(contains(null));
       @ also public normal_behavior
       @   requires contains(o);
       @   assignable _theCollection;
       @   ensures !\result;
       @   ensures !contains(o);
       @   ensures \old(contains(null)) <==> (contains(null) || o==null);
       @   ensures (\forall Object oo; \old(contains(oo)) <==> 
                                (contains(oo) || o == oo));
       @   ensures size() == \old(size()) - 1;
       @*/
    boolean remove(/*@nullable*/ Object o);

    // Bulk Operations

    /*+@ also
       @ public behavior
       @   requires c instanceof Set;
       @   ensures \result ==> ((Set) c).theSet.isSubset(theSet);
       @*/
    //@ pure
    boolean containsAll(Collection c);

    /*+@ also
       @ public behavior
       @   assignable theCollection;
       @   ensures 
       @        theSet.equals(\old(theSet).union(JMLEqualsSet.convertFrom(c)))
       @        && (\result ==> !theSet.equals(\old(theSet)));
       @*/
    /*-@ also public normal_behavior
       @   assignable _theCollection;
       @   ensures contains(null) <==> (\old(contains(null)) || \old(c.contains(null)));
       @   ensures (\forall Object o; contains(o) <==>
                      (\old(contains(o)) || \old(c.contains(o))));
       @   ensures size() >= \old(size());
       @*/
    boolean addAll(Collection c);

    /*+@ also
       @ public behavior
       @   assignable theCollection;
       @   ensures theSet.equals(\old(theSet).intersection(
       @                                  JMLEqualsSet.convertFrom(c)))
       @        && (\result ==> !theSet.equals(\old(theSet)));
       @*/
    /*-@ also public normal_behavior
       @   assignable _theCollection;
       @   ensures contains(null) <==> (\old(contains(null)) && \old(c.contains(null)));
       @   ensures (\forall Object o; contains(o) <==>
                      (\old(contains(o)) && \old(c.contains(o))));
       @   ensures size() <= \old(size());
       @*/
    boolean retainAll(Collection c);

    /*+@ also
       @ public behavior
       @   assignable theCollection;
       @   ensures theSet.equals(\old(theSet).difference(
       @                                  JMLEqualsSet.convertFrom(c)))
       @        && (\result ==> !theSet.equals(\old(theSet)));
       @*/
    /*-@ also public normal_behavior
       @   assignable _theCollection;
       @   ensures contains(null) <==> (\old(contains(null)) && !\old(c.contains(null)));
       @   ensures (\forall Object o; contains(o) <==>
                      (\old(contains(o)) && !\old(c.contains(o))));
       @   ensures size() <= \old(size());
       @*/
    boolean removeAll(Collection c);

    // specification inherited
    void clear();

    // Comparison and hashing

    /*+@ also
       @ public normal_behavior
       @   requires o instanceof Set;
       @   ensures \result ==> theSet.equals(((Set)o).theSet);
       @*/
    /*-@ also public normal_behavior
       @   requires o instanceof Set;
       @   ensures \result <==>
               ((\forall Object o; contains(o) <==> ((Set)o).contains(o))
             && contains(null) <==> ((Set)o).contains(null));
       @   ensures_redundantly \result ==> (size == ((Set)o).size());
       @*/
    /*@ pure @*/ boolean equals(/*@ nullable @*/ Object o);

    // specification inherited
    int hashCode();
}
