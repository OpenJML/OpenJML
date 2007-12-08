// @(#)$Id: List.spec,v 1.35 2006/12/11 21:16:18 chalin Exp $

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

//@ model import org.jmlspecs.models.*;

/** JML's specification of java.util.List.
 * @version $Revision: 1.35 $
 * @author Brandon Shilling
 * @author Gary T. Leavens
 */
public interface List extends Collection {

    /*+@ public model instance non_null JMLEqualsSequence theList;
      @                                               in theCollection;
      @ public instance represents theCollection <- theList.toBag();
      @*/
    /*-@ public model instance non_null Object[] _theList; in _theCollection;
      @  public instance represents _theCollection <- _theList;
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

    /*+@ also
      @ public behavior
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures size() < Integer.MAX_VALUE
      @       ==> (\forall int i; 0 <= i && i < size();
      @                \result.hasNext(i) && \result.nthNextElement(i)
      @                 == toArray()[i]);
      @*/
    /*@ pure @*/ Iterator iterator();

    /*+@ also
      @  public normal_behavior
      @   requires size() < Integer.MAX_VALUE;
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures \result.length == size();
      @   ensures (\forall int i; 0 <= i && i < size();
      @                 \result[i].equals(theList.get(i)));
      @*/
    //@ pure
    Object[] toArray();

    /*+@ also
      @ public normal_behavior
      @   old int colSize = theCollection.int_size();
      @   old int arrSize = a.length;
      @   requires a!= null && colSize < Integer.MAX_VALUE;
      @   requires elementType <: \elemtype(\typeof(a));
      @   requires (\forall Object o; contains(o); \typeof(o) <: \elemtype(\typeof(a)));
      @   {|
      @     requires colSize <= arrSize;
      @     assignable a[*];
      @     ensures \result == a;
      @     ensures (\forall int k; 0 <= k && k < colSize;
      @                  theList.get(k) == \result[k]);
      @     ensures (\forall int i; colSize <= i && i < arrSize;
      @                             \result[i] == null);
      @   also
      @     requires colSize > arrSize;
      @     assignable \nothing;
      @     ensures \fresh(\result) && \result.length == colSize;
      @     ensures (\forall int k; 0 <= k && k < colSize;
      @                             theList.get(k) == \result[k]);
      @   |}
      @*/
    Object[] toArray(Object[] a);

    /*+@ also
      @   public behavior
      @     assignable theCollection;
      @     ensures \result && theList.equals(\old(theList).insertBack(o));
      @*/
    boolean add(/*@nullable*/ Object o);

    /*+@ also
      @   public behavior
      @     assignable theCollection;
      @     ensures \result
      @          ==> theList
      @              .equals(\old(theList.removeItemAt(theList.indexOf(o))));
      @*/
    boolean remove(/*@nullable*/ Object o);

    // specification inherited
    //@ pure
    boolean containsAll(Collection c);

    // specification inherited
    boolean addAll(Collection c);

    /*+@   public behavior
      @     requires c != null;
      @     requires 0 <= index && index <= size();
      @     requires c.elementType <: elementType;
      @     requires !containsNull ==> !c.containsNull;
      @     assignable theCollection;
      @     ensures \result
      @         ==> theList.equals(
      @                     \old(theList.subsequence(0,index))
      @                      .concat(JMLEqualsSequence.convertFrom(c))
      @                      .concat(\old(theList.subsequence(index,size()))));
      @     signals_only UnsupportedOperationException,
      @                  IllegalArgumentException;
      @     signals (UnsupportedOperationException)
      @              (* if this operation is not supported *);
      @     signals (IllegalArgumentException)
      @              (* if some aspect of c prevents
      @                 its elements from being added to the list *);
      @ also
      @   public exceptional_behavior
      @     requires c == null || !(0 <= index && index <= size())
      @             || !(c.elementType <: elementType)
      @             || (!containsNull && c.containsNull);
      @     assignable \nothing;
      @     signals_only UnsupportedOperationException,
      @                  ClassCastException, NullPointerException,
      @                  IndexOutOfBoundsException;
      @     signals (ClassCastException)
      @             c != null && !(c.elementType <: elementType);
      @     signals (NullPointerException) c == null;
      @     signals (IndexOutOfBoundsException)
      @             !(0 <= index && index <= size());
      @*/
    boolean addAll(int index, Collection c);

    // specification inherited
    boolean removeAll(Collection c);

    // specification inherited
    boolean retainAll(Collection c);

    // specification inherited
    void clear();

    /*+@ also
      @ public normal_behavior
      @   requires o instanceof List && size() == ((List) o).size();
      @   assignable \nothing;
      @   ensures \result
      @       ==> (\forall int i; 0 <= i && i < size(); 
      @                (theList.get(i) == null
      @                 && ((List) o).theList.get(i) == null) 
      @             || (theList.get(i).equals(((List) o).theList.get(i))));
      @ also public normal_behavior
      @   requires !(o instanceof List && size() == ((List) o).size());
      @   assignable \nothing;
      @   ensures !\result;
      @*/
    /*@ pure @*/ boolean equals(/*@ nullable @*/ Object o);

    // specification inherited
    int hashCode();

    /*+@ public normal_behavior
      @   requires 0 <= index && index < size();
      @   assignable \nothing;
      @   ensures \result == theList.get(index);
      @ also
      @ public exceptional_behavior
      @   requires !(0 <= index && index < size());
      @   assignable \nothing;
      @   signals_only IndexOutOfBoundsException;
      @
      @ implies_that
      @   public normal_behavior
      @     requires index >= 0;
      @     ensures (\result == null) || \typeof(\result) <: elementType;
      @     ensures !containsNull ==> \result != null;
      @*/
    /*@ pure @*/ Object get(int index);

    /*+@
      @ public behavior
      @ requires !containsNull ==> element != null;
      @ requires (element == null) || \typeof(element) <: elementType;
      @ {|
      @   requires 0 <= index && index < size();
      @   assignable theCollection;
      @   ensures \result == (\old(theList.get(index)));
      @   ensures theList.equals(
      @              \old(theList.subsequence(0,index))
      @                   .insertBack(element)
      @                   .concat(\old(theList.subsequence(index+1,size()))));
      @   signals_only UnsupportedOperationException, ClassCastException,
      @                NullPointerException, IllegalArgumentException;
      @   signals (UnsupportedOperationException)
      @           (* set method not supported by list *);
      @   signals (ClassCastException)
      @           (* class of specified element prevents it
      @              from being added to this *);
      @   signals (NullPointerException)
      @            (* element is null and null elements
      @               not supported by this *);
      @   signals (IllegalArgumentException)
      @            (* some aspect of element prevents it
      @               from being added to this *);
      @ also
      @   requires !(0 <= index && index < size());
      @   assignable \nothing;
      @   ensures false;
      @   signals_only UnsupportedOperationException,
      @                IndexOutOfBoundsException;
      @ |}
      @*/
    Object set(int index, Object element);
    
    /*+@ public behavior
      @   requires !containsNull ==> element != null;
      @   requires (element == null) || \typeof(element) <: elementType;
      @   {|
      @     requires  0 <= index && index <= size();
      @     assignable theCollection;
      @     ensures (element == null && theList.get(index) == null)
      @          || (theList.get(index).equals(element))
      @          && (\forall int i; 0 <= i && i < index;
      @                     (theList.get(i) == null
      @                      && \old(theList).get(i) == null)    
      @                  || theList.get(i).equals(\old(theList.get(i))))
      @          && (\forall int i; index <= i && i < \old(size());
      @                     (theList.get((int)(i+1)) == null
      @                      && \old(theList).get(i) == null)    
      @                  || theList.get((int)(i+1))
      @                                        .equals(\old(theList.get(i))));
      @     signals_only UnsupportedOperationException, ClassCastException,
      @                  NullPointerException, IllegalArgumentException;
      @     signals (UnsupportedOperationException)
      @             (* add method not supported by list *);
      @     signals (ClassCastException)
      @             (* class of specified element prevents it
      @                from being added to this *);
      @     signals (NullPointerException)
      @             (* element is null and null elements are not
      @                supported by this *);
      @     signals (IllegalArgumentException)
      @             (* some aspect of element
      @                prevents it from being added to this *);
      @ also
      @   requires !(0 <= index && index <= size());
      @   assignable \nothing;
      @   ensures false;
      @   signals_only UnsupportedOperationException,
      @                IndexOutOfBoundsException;
      @ |}
      @*/
    void add(int index, Object element);

    /*+@ public behavior
      @ {|
      @   requires  0 <= index && index < size();
      @   assignable theCollection;
      @   ensures \result == (\old(theList.get(index))) ;
      @   ensures (\forall int i; 0 <= i && i < index;
      @                   (theList.get(i) == null
      @                    && \old(theList).get(i) == null)    
      @                || theList.get(i) == (\old(theList.get(i))))
      @        && (\forall \bigint i; index <= i && i < (\old(size() - 1) );
      @                   (theList.get((int)i) == null
      @                    && \old(theList).get((int)(i+1)) == null)    
      @                || theList.get((int)i) == (\old(theList.get((int)(i+1)))));
      @   signals_only UnsupportedOperationException;
      @   signals (UnsupportedOperationException)
      @            (* remove method not supported by list *);
      @ also
      @   requires  0 <= index && index < size();
      @   assignable theCollection;
      @   ensures (\result == null) || \typeof(\result) <: elementType;
      @   ensures !containsNull ==> \result != null;
      @ also
      @   requires !(0 <= index && index < size());
      @   assignable \nothing;
      @   ensures false;
      @   signals_only UnsupportedOperationException,
      @                IndexOutOfBoundsException;
      @ |}
      @*/
    Object remove(int index);

    /*+@ public behavior
      @   requires !containsNull ==> o != null;
      @   requires (o == null) || \typeof(o) <: elementType;
      @   assignable \nothing;
      @   ensures \result != -1 && theList.get(\result) == null
      @           ==> o == null;
      @   ensures \result != -1 && theList.get(\result) != null
      @           ==> theList.get(\result).equals(o)
      @               && theList.indexOf(o) == \result;
      @   ensures \result == -1 && !contains(o);
      @   signals_only ClassCastException, NullPointerException;
      @   signals (ClassCastException)
      @           (* class of specified element is incompatible with this *);
      @   signals (NullPointerException)
      @            (* element is null and null elements are not
      @               supported by this *);
      @ implies_that
      @   ensures \result != -1
      @       ==> (\forall int i; 0 <= i && i < \result;
      @                 (theList.get(i) == null && o != null)
      @              || (theList.get(i) != null && !theList.get(i).equals(o)));
      @*/
    /*@ pure @*/ int indexOf(Object o);

    /*+@ public behavior
      @   requires !containsNull ==> o != null;
      @   requires (o == null) || \typeof(o) <: elementType;
      @   assignable \nothing;
      @   ensures \result != -1 && theList.get(\result) == null
      @           ==> o == null;
      @   ensures \result != -1 && theList.get(\result) != null 
      @            ==> theList.get(\result).equals(o)
      @                && theList.reverse().indexOf(o)
      @                   == theList.int_size() - (\result + 1); 
      @   signals_only ClassCastException, NullPointerException;
      @   signals (ClassCastException)
      @           (* class of specified element is incompatible with this *);
      @   signals (NullPointerException)
      @           (* element is null and null elements are not
      @              supported by this *);
      @ implies_that
      @   ensures \result != -1
      @       ==> (\forall int i; \result < i && i < theList.int_size();
      @                 (theList.get(i) == null && o != null)
      @              || (theList.get(i) != null && !theList.get(i).equals(o)));
      @*/
    /*@ pure @*/ int lastIndexOf(Object o);

    /*+@ 
      @ public normal_behavior
      @   assignable \nothing;
      @   ensures \result != null && size() < Integer.MAX_VALUE
      @       ==> (\forall int i; 0 <= i && i < size();
      @                \result.hasNext(i) && \result.nthNextElement(i)
      @                 == toArray()[i]);
      @   ensures \result.elementType == elementType;
      @   ensures containsNull == \result.returnsNull;
      @*/
    /*@ pure @*/ /*@ non_null @*/ ListIterator listIterator();

    /*+@ 
      @ public normal_behavior
      @   requires 0 <= index && index < size();
      @   assignable \nothing;
      @   ensures \result != null && size() < Integer.MAX_VALUE
      @       ==> (\forall int i; index <= i && i < size();
      @                \result.hasNext(i) && \result.nthNextElement(i)
      @                 == toArray()[i]);
      @ also
      @ public exceptional_behavior
      @   requires index < 0 && size() <= index;
      @   signals_only IndexOutOfBoundsException;
      @
      @  implies_that
      @     ensures \result.elementType == elementType;
      @     ensures containsNull == \result.returnsNull;
      @*/
    /*@ pure @*/ /*@ non_null @*/ ListIterator listIterator(int index);

    /*+@ public normal_behavior
      @   requires 0 <= fromIndex && fromIndex <= size() 
      @         && 0 <= toIndex && toIndex <= size()
      @         && fromIndex <= toIndex;
      @   assignable \nothing;
      @   ensures \result != null
      @        && \result.theList
      @             .equals(theList.subsequence(fromIndex, toIndex));
      @ also
      @ public exceptional_behavior
      @   requires !(0 <= fromIndex && fromIndex <= size())
      @         || !( 0 <= toIndex && toIndex <= size())
      @         || !(fromIndex <= toIndex);
      @   assignable \nothing;
      @   signals_only IndexOutOfBoundsException;
      @
      @ implies_that
      @   public normal_behavior
      @     requires 0 <= fromIndex && fromIndex <= toIndex;
      @*/
    /*@ pure @*/ List subList(int fromIndex, int toIndex);
}
