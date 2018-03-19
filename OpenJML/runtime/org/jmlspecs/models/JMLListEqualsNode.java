// @(#)$Id: JMLListNode.java-generic,v 1.56 2006/12/02 23:38:15 leavens Exp $

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

/** An implementation class used in various models.  These are
 * singly-linked list nodes containing objects.  The empty
 * list is represented by null, which makes dealing with these lists
 * tricky.  Normal users should use {@link JMLEqualsSequence} instead of this
 * type to avoid these difficulties.
 *
 * <p>
 * This type uses ".equals" to compare elements. The cons method
 * does not clone elements that are passed into the list.
 *
 * @version $Revision: 1.56 $
 * @author Gary T. Leavens
 * @author Albert L. Baker
 * @see JMLEqualsSequence
 * @see JMLEqualsBag
 * @see JMLEqualsSet
 */
//+OPENJML@ immutable
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
/*@ pure spec_public @*/ class JMLListEqualsNode implements JMLType {

    //*********************** equational theory ***********************

    /*@ public invariant (\forall JMLListEqualsNode l2;
      @                    (\forall Object e1, e2;
      @                     (\forall \bigint n;
      @                    equational_theory(this, l2, e1, e2, n) )));
      @*/

    /** An `equational' specification of lists, for use in the invariant.
     */
    /*@ public normal_behavior
      @ {|
      @    // The following define itemAt and size.  The behavior 
      @	   // of the other methods is defined based by these two 
      @    // methods.
      @ 
      @    ensures \result <==>
      @       (new JMLListEqualsNode(e1, null)).size() == 1;
      @  also
      @    ensures \result <==>
      @        (ls != null)
      @          ==> (new JMLListEqualsNode(e1, ls)).size() == 1 + ls.size();
      @  also
      @    ensures \result <==>
      @        (ls != null)
      @          ==> (ls.next == null) == (ls.size() == 1);
      @  also
      @    ensures \result <==>
      @        ls != null && ls.next != null 
      @          ==> ls.size() == 1 + ls.next.size();
      @  also
      @    ensures \result <==>
      @        (ls != null && ls.val != null)
      @          ==> ls.val.equals(ls.head());
      @  also
      @    ensures \result <==>
      @        (e1 != null)
      @          ==> cons(e1, ls).head().equals(e1);
      @  also
      @    ensures \result <==>
      @        (ls != null && ls.val != null)
      @          ==> ls.itemAt(0).equals(ls.head());
      @  also
      @    ensures \result <==>
      @        ls != null && 0 < n && n < ls.size()
      @          ==> ls.itemAt(n).equals(ls.next.itemAt(n - 1));
      @ |}
      public pure model boolean equational_theory(
                       JMLListEqualsNode ls, JMLListEqualsNode ls2,
                       Object e1, Object e2, \bigint n);
      @*/

    //@ public model JMLDataGroup elementState;

    /** The data contained in this list node.
     */
    public final Object val;
    //@ in objectState; maps val.objectState \into elementState;

    /** The next node in this list.
     */
    public final JMLListEqualsNode next;
    //@ in objectState; maps next.elementState \into elementState;

    /** The type of the elements in this list.  This type is an upper
     * bound on the element's types. The type is computed
     * pessimistically, so that the order of adding elements does not
     * matter; that is, if any element in the list is null, then we
     * use Object as the type of the list's elements.
     */
    //@ ghost public \TYPE elementType;

    //@ public constraint elementType == \old(elementType);

    //@ public invariant elementType <: \type(Object);

    //@ public invariant val != null ==> \typeof(val) <: elementType;
    //@ public invariant val == null ==> \type(Object) == elementType;
    /*@ public invariant_redundantly
      @         containsNull ==> \type(Object) == elementType;
      @*/
    //@ public invariant next != null ==> next.elementType <: elementType;

    /** Whether this list can contain null elements;
     */
    //@ ghost public boolean containsNull;

    //@ public constraint containsNull == \old(containsNull);

    //@ public invariant containsNull <==> has(null);

    /*@ protected
      @    invariant containsNull <==>
      @              val == null || (next != null && next.containsNull);
      @*/

    //@ public invariant owner == null;

    //************************* Constructors ********************************

    /** Initialize this list to have the given item as its first
     * element followed by the given list.
     * This does not do any cloning.
     *
     * @param item the object to place at the head of this list.
     * @param nxt the _JMLListEqualsNode to make the tail of this list.
     */
    /*@  public normal_behavior
      @    requires item != null;
      @    assignable val, next, elementType, containsNull, owner;
      @    ensures val.equals(item) && next == nxt
      @         && \typeof(item) <: elementType
      @         && (nxt != null ==> nxt.elementType <: elementType)
      @         && (nxt == null ==> elementType == \typeof(item))
      @         && containsNull == (nxt == null ? false : nxt.containsNull);
      @ also
      @  public normal_behavior
      @    requires item == null;
      @    assignable val, next, elementType, containsNull, owner;
      @    ensures val == null && next == nxt
      @         && elementType == \type(Object)
      @         && containsNull;
      @
      @ implies_that
      @    ensures val == item && next == nxt;
      @    ensures item == null ==> containsNull;
      @    ensures item != null && nxt != null
      @            ==> containsNull == nxt.containsNull;
      @*/
    public JMLListEqualsNode(Object item, JMLListEqualsNode nxt) {
        //@ set owner = null;
        val = item;
        next = nxt;
        /*@ set elementType
          @     = (item == null 
          @         ? \type(Object)
          @         : (nxt == null ? \typeof(item)
          @                        : ((\typeof(item) <: nxt.elementType)
          @                            ? nxt.elementType
          @                            // types aren't totally ordered!
          @                            : ((nxt.elementType <: \typeof(item))
          @                               ? \typeof(item)
          @                               : \type(Object)))));
          @*/
        /*@ set containsNull
          @       = (val == null || (next != null && next.containsNull));
          @*/
    } //@ nowarn Invariant;

    /** Return a JMLListEqualsNode containing the given element
     *  followed by the given list.
     *
     * Note that cons() adds elements to the front of a list.  
     * It handles any necessary cloning for value lists and it handles 
     * inserting null elements.
     *
     * @param hd the object to place at the head of the result.
     * @param tl the JMLListEqualsNode to make the tail of the result.
     */
    /*@  public normal_behavior
      @    ensures \result.headEquals(hd) && \result.next == tl;
      @    ensures \result.equals(new JMLListEqualsNode(hd, tl));
      @
      @ implies_that public normal_behavior
      @    ensures \result != null
      @         && \result.containsNull <==>
      @             hd == null || (tl != null && tl.containsNull);
      @*/
    public static /*@ pure @*/
        JMLListEqualsNode cons(/*@ nullable @*/ Object hd, /*@ nullable @*/ JMLListEqualsNode tl) {
        if (hd == null) {
            JMLListEqualsNode ret = new JMLListEqualsNode(null, tl);
            //@ assume ret.containsNull;
            return ret;
        } else {
            Object h = hd ;
            //@ assume h != null && h instanceof Object;
            JMLListEqualsNode ret = new JMLListEqualsNode((Object)h, tl);
            //@ assume ret.containsNull <==> tl != null && tl.containsNull;
            return ret;
        }
    }

    //**************************** Observers **********************************

    /** Return the first element in this list.
     * Note that head() handles any cloning necessary for value lists.
     */
    /*@  public normal_behavior
      @    requires val != null;
      @    ensures \result != null && \result.equals(val);
      @ also
      @  public normal_behavior
      @    requires val == null;
      @    ensures \result == null;
      @
      @ implies_that
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @*/
    public Object head() {
        Object ret = (val == null
                          ? null
                          : (Object)val ); //@ nowarn Cast;
        //@ assume ret != null ==> \typeof(ret) <: elementType;
        //@ assume !containsNull ==> ret != null;
        return ret;
    }

    /** Tell if the head of the list is ".equals" to the given
     * item.
     * @see #has(Object)
     */
    /*@  public normal_behavior
      @    requires val != null;
      @    ensures \result == (val.equals(item));
      @ also
      @  public normal_behavior
      @    requires val == null;
      @    ensures \result == (item == null);
      @*/
    public boolean headEquals(Object item) {
        return elem_equals(val, item);
    }

    /** Tell if the given elements are equal, taking null into account.
     */
    private static /*@ pure @*/ boolean elem_equals(Object item1,
                                                      Object item2) {
        return (item1 != null && item1.equals(item2))
	    || (item1 == null && item2 == null);
    }

    /** Return the ith element of a list.
     * @see #getItem(\bigint)
     */
    /*@  public normal_behavior
      @    requires 0 <= i && i < length();
      @    ensures \result != null ==>
      @                (* \result ".equals" the ith element of this *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length());
      @    signals_only JMLListException;
      @
      @ implies_that
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @*/
    /*@
      model public Object itemAt(\bigint i) throws JMLListException {
        if (i < 0) {
            throw new JMLListException("Index to itemAt(int) is negative "
                                       + i);
        } else {
            \bigint k = i;
              assert k >= 0;
            JMLListEqualsNode ptr = this;
              maintaining k >= 0;
              decreasing k;
            while (ptr != null && k > 0) {
                k = k - 1;
                ptr = ptr.next;
            }
            if (ptr == null) {
                throw new JMLListException("Index to itemAt(\bigint) out of range.");
            } else {
                  assert ptr != null && k == 0;
                  assume ptr.val != null
                          ==> \typeof(ptr.val) <: \type(Object);
                  
                Object ret = (ptr.val == null
                                  ? null
                                  : (Object)(ptr.val) );
                  assume ret != null ==> \typeof(ret) <: elementType;
                  assume !containsNull ==> ret != null;
                return ret;
            }
        }
    }
    @*/

    /** Return the ith element of a list.
     * @see #getItem(Object)
     */
    /*@  public normal_behavior
      @    requires 0 <= i && i < int_length();
      @    ensures \result != null ==>
      @                (* \result ".equals" the ith element of this *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < int_length());
      @    signals_only JMLListException;
      @
      @ implies_that
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @*/
    public Object itemAt(int i) throws JMLListException {
        if (i < 0) {
            throw new JMLListException("Index to itemAt(int) is negative "
                                       + i);
        } else {
            int k = i;
            //@ assert k >= 0;
            JMLListEqualsNode ptr = this;
            //@ maintaining k >= 0;
            //@ decreasing k;
            while (ptr != null && k > 0) {
                k--;
                ptr = ptr.next;
            }
            if (ptr == null) {
                throw new JMLListException("Index to itemAt(int) out of range.");
            } else {
                //@ assert ptr != null && k == 0;
                /*@ assume ptr.val != null
                  @        ==> \typeof(ptr.val) <: \type(Object);
                  @*/
                Object ret = (ptr.val == null
                                  ? null
                                  : (Object)(ptr.val) );
                //@ assume ret != null ==> \typeof(ret) <: elementType;
                //@ assume !containsNull ==> ret != null;
                return ret;
            }
        }
    }

    /** Tells the number of elements in the sequence; a synonym for length
     */
    /*@  public normal_behavior
      @    ensures (* \result is the number of JMLListEqualsNode(s) in this *);
      @
      @ implies_that
      @    ensures \result > 0;
      @*/
    /*@
      @ public model pure \bigint size() {
          \bigint count = 0;
	  JMLListEqualsNode ptr = this;
	    maintaining (* ptr is count next's from this *);
	  while (ptr != null) {
	    ptr = ptr.next;
            count = count + 1;
          }
          return count;
      @ } 
      @*/

    /** Tells the number of elements in the sequence; a synonym for length
     */
    /*@  public normal_behavior
      @    ensures \result == size();
      @
      @ implies_that
      @    ensures \result > 0;
      @*/
    /*@
      @ public model pure \bigint length() {
      @   return size();
      @ } 
      @*/

    /** Tells the number of elements in the list; a synonym for length.
     */
    /*@  public normal_behavior
      @    ensures \result == size();
      @
      @ implies_that
      @    ensures \result > 0;
      @*/
    public int int_size() {
        int count = 0;
        JMLListEqualsNode ptr = this;
        //@ maintaining (* ptr is count next's from this *);
        while (ptr != null) {
            ptr = ptr.next;
            count++;
        }
        return count;
    }

    /** Tells the number of elements in the list; a synonym for size.
     */
    /*@  public normal_behavior
      @    ensures \result == length();
      @
      @ implies_that
      @    ensures \result > 0;
      @*/
    public int int_length() {
        return int_size();
    }

    /** Tells whether the given element is ".equals" to an
     * element in the list.
     */
    /*@  public normal_behavior
      @    requires item != null;
      @    ensures \result <==> 
      @               (\exists int i; 0 <= i && i < int_length();
      @                           (itemAt(i) == null
      @                             ? item == null
      @                             : itemAt(i).equals(item)));
      @ also
      @  public normal_behavior
      @    requires item == null;
      @    ensures \result <==> 
      @               (\exists int i; 0 <= i && i < int_length();
      @                               itemAt(i) == null);
      @*/
    public boolean has(Object item) {
        JMLListEqualsNode ptr = this;
        //@ maintaining (* no earlier element is elem_equals to item *);
        while (ptr != null) {
            if (elem_equals(ptr.val, item)) {
                return true;
            }
            ptr = ptr.next;
        }
        return false;
    }

    /** Tells whether the elements of this list occur, in
     *  order, at the beginning of the given list, using ".equals" for
     *  comparisons.
     */
    /*@  public normal_behavior
      @    requires ls2 != null;
      @    ensures \result <==>
      @       int_length() <= ls2.int_length()
      @       && (\forall int i; 0 <= i && i < int_length();
      @                          (ls2.itemAt(i) == null && itemAt(i) == null)
      @                       || (ls2.itemAt(i) != null &&
      @                           ls2.itemAt(i).equals(itemAt(i))));
      @ also
      @  public normal_behavior
      @    requires ls2 == null;
      @    ensures !\result;
      @*/
    public boolean isPrefixOf(JMLListEqualsNode ls2) {
        if (ls2 == null) {
            return false;
        }
        JMLListEqualsNode othLst = ls2;
        JMLListEqualsNode thisLst = this;
        /*@ maintaining
          @ (* all earlier elements of both lists are elem_equals *);
          @*/
        while (thisLst != null && othLst != null) {
            if (!elem_equals(thisLst.val, othLst.val)) {
                return false;
            }
            thisLst = thisLst.next;
            othLst = othLst.next;
        }
        return thisLst == null;
    }

    /** Test whether this object's value is equal to the given argument.
     */
    /*@ also
      @  public normal_behavior
      @     requires ls2 != null && ls2 instanceof JMLListEqualsNode;
      @     ensures \result <==> isPrefixOf((JMLListEqualsNode)ls2)
      @                           && ((JMLListEqualsNode)ls2).isPrefixOf(this);
      @ also
      @  public normal_behavior
      @    requires ls2 == null || !(ls2 instanceof JMLListEqualsNode);
      @    ensures \result <==> false;
      @*/
    public boolean equals(/*@ nullable @*/ Object ls2) {
        if (ls2 != null && ls2 instanceof JMLListEqualsNode) {
            JMLListEqualsNode othLst = (JMLListEqualsNode)ls2;
            JMLListEqualsNode thisLst = this;
            //@ maintaining (* all earlier elements of both lists are elem_equals *);
            while (thisLst != null && othLst != null) {
                if (!elem_equals(thisLst.val, othLst.val)) {
                    return false;
                }
                thisLst = thisLst.next;
                othLst = othLst.next;
            }
            return (othLst == thisLst); // both must be null.
        } else {
            return false;
        }
    }

    /** Return a hash code for this object.
     */
    public int hashCode() {
        int hash = 0;
        JMLListEqualsNode ptr = this;
        while (ptr != null) {
            Object v = ptr.val;
            if (v != null) {
                hash += v.hashCode();
            }
            ptr = ptr.next;
        }
        return hash;
    }

    /** Return the zero-based index of the first occurrence of the given
     *  element in the list, if there is one
     *  @param item the Object sought in this.
     *  @return the first index at which item occurs or -1 if it does not.
     */
    /*@  public normal_behavior
      @    requires has(item) && item != null;
      @    ensures itemAt(\result).equals(item)
      @          && (\forall \bigint i; 0 <= i && i < \result;
      @                             !(itemAt(i) != null
      @                               && itemAt(i).equals(item)));
      @    ensures_redundantly
      @          (* \result is the first index at which item occurs in this *);
      @ also
      @  public normal_behavior
      @    requires has(item) && item == null;
      @    ensures itemAt(\result) == null
      @          && (\forall \bigint i; 0 <= i && i < \result;
      @                             itemAt(i) != null);
      @    ensures_redundantly
      @          (* \result is the first index at which null occurs in this *);
      @ also
      @  public normal_behavior
      @    requires !has(item);
      @    ensures \result == -1;
      @
      @ implies_that
      @   ensures \result >= -1;
      @*/
    /*@
    model public \bigint bi_indexOf(Object item) {
        \bigint idx = 0;
        JMLListEqualsNode ptr = this;
         maintaining (* ptr is idx next's from this *);
        while (ptr != null) {
            if (elem_equals(ptr.val, item)) {
                return idx;
            }
            ptr = ptr.next;
            idx = idx + 1;
        }
        return -1;
    }
    @*/

    /** Return the zero-based index of the first occurrence of the given
     *  element in the list, if there is one
     *  @param item the Object sought in this.
     *  @return the first index at which item occurs or -1 if it does not.
     */
    /*@  public normal_behavior
      @    requires has(item) && item != null;
      @    ensures itemAt(\result).equals(item)
      @          && (\forall int i; 0 <= i && i < \result;
      @                             !(itemAt(i) != null
      @                               && itemAt(i).equals(item)));
      @    ensures_redundantly
      @          (* \result is the first index at which item occurs in this *);
      @ also
      @  public normal_behavior
      @    requires has(item) && item == null;
      @    ensures itemAt(\result) == null
      @          && (\forall int i; 0 <= i && i < \result;
      @                             itemAt(i) != null);
      @    ensures_redundantly
      @          (* \result is the first index at which null occurs in this *);
      @ also
      @  public normal_behavior
      @    requires !has(item);
      @    ensures \result == -1;
      @
      @ implies_that
      @   ensures \result >= -1;
      @*/
    public int indexOf(Object item) {
        int idx = 0;
        JMLListEqualsNode ptr = this;
        //@ maintaining (* ptr is idx next's from this *);
        while (ptr != null) {
            if (elem_equals(ptr.val, item)) {
                return idx;
            }
            ptr = ptr.next;
            idx++;
        }
        return -1;
    }

    /** Return the last element in this list.
     */
    /*@  public normal_behavior
      @    ensures (\result == null && itemAt((int)(int_length()-1)) == null)
      @          || \result.equals(itemAt((int)(int_length()-1)));
      @
      @ implies_that
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @*/
    public Object last() {
        if (next == null) {
            return head();
        } else {
            JMLListEqualsNode ptr = this;
            //@ maintaining ptr != null;
            while (ptr.next != null) {
                ptr = ptr.next;
            }
            //@ assert ptr.next == null;
            //@ assume ptr.val != null ==> \typeof(ptr.val) <: \type(Object);
            Object ret = (ptr.val == null
                              ? null
                              : (Object)(ptr.val) );
            //@ assume ret != null ==> \typeof(ret) <: elementType;
            //@ assume !containsNull ==> ret != null;
            return ret;
        }
    }

    /** Return the zero-based index of the first occurrence of the given
     *  element in the list, if there is one
     *  @param item the Object sought in this list.
     *  @return the first zero-based index at which item occurs.
     *  @exception JMLListException if the item does not occur in this list.
     *  @see #itemAt(int)
     */
    /*@  public normal_behavior
      @    requires has(item);
      @    {|
      @       requires item != null;
      @       ensures \result.equals(itemAt(indexOf(item)));
      @      also
      @       requires item == null;
      @       ensures \result == null;
      @     |}
      @ also
      @  public exceptional_behavior
      @    requires !has(item);
      @    signals_only JMLListException;
      @ implies_that
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @*/
    public Object getItem(Object item) throws JMLListException {
        JMLListEqualsNode ptr = this;
        //@ maintaining (* no earlier element is elem_equals to item *);
        while (ptr != null) {
            if (elem_equals(ptr.val, item)) {
                //@ assume ptr.val != null ==> \typeof(ptr.val) <: elementType;
                return ptr.val;
            }
            ptr = ptr.next;
        }
        throw new JMLListException("No matching item in list.");
    }

    // ******************** building new JMLEqualsLists ***********************
             
    /** Return a clone of this object.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result != null && \result instanceof JMLListEqualsNode
      @            && ((JMLListEqualsNode)\result).equals(this);
      @*/
    public /*@ non_null @*/ Object clone() {
        return this;
    } //@ nowarn Post;

    /** Return a list containing the first n elements in this list.
     *  @param n the number of elements to leave in the result.
     *  @return null if n is not positive or greater than the length of this list.
     */
    /*@  public normal_behavior
      @  {|
      @     requires 0 < n && n <= length();
      @     ensures \result != null
      @         && \result.length() == n
      @         && (\forall \bigint i; 0 <= i && i < n;
      @                            \result.itemAt(i) == itemAt(i));
      @   also
      @     requires n <= 0;
      @     ensures \result == null;
      @   also
      @     requires length() < n;
      @     ensures this.equals(\result);
      @  |}
      @ implies_that
      @    ensures !containsNull && \result != null ==> !\result.containsNull;
      @*/   
    /*@
    model public JMLListEqualsNode prefix(\bigint n) {
        return (n <= 0 
                ? null 
                : new JMLListEqualsNode(val, 
                                        (next == null ? null 
                                         : next.prefix(n-1)))
                );
    }
    @*/

    /** Return a list containing the first n elements in this list.
     *  @param n the number of elements to leave in the result.
     *  @return null if n is not positive or greater than the length of this list.
     */
    /*@  public normal_behavior
      @  {|
      @     requires 0 < n && n <= int_length();
      @     ensures \result != null
      @         && \result.int_length() == n
      @         && (\forall int i; 0 <= i && i < n;
      @                            \result.itemAt(i) == itemAt(i));
      @   also
      @     requires n <= 0;
      @     ensures \result == null;
      @   also
      @     requires int_length() < n;
      @     ensures this.equals(\result);
      @  |}
      @ implies_that
      @    ensures !containsNull && \result != null ==> !\result.containsNull;
      @*/
    public JMLListEqualsNode prefix(int n) {
        return (n <= 0 
                ? null 
                : new JMLListEqualsNode(val, 
                                        (next == null ? null 
                                         : next.prefix(n-1)))
                );
    }

    /** Return a list containing all but the first n elements in this list.
     *  @param n the number of elements to remove
     *  @return null if n is negative or greater than the length of this list.
     */
    /*@  public normal_behavior
      @  {|
      @     requires 0 < n && n < length();
      @     ensures \result != null
      @          && \result.length() == length() - n
      @          && (\forall \bigint i; n <= i && i < length();
      @                             \result.itemAt(i-n) == itemAt(i));
      @   also
      @     requires n <= 0;
      @     ensures this.equals(\result);
      @   also
      @     requires length() <= n;
      @     ensures \result == null;
      @  |}
      @
      @ implies_that
      @    ensures !containsNull && \result != null ==> !\result.containsNull;
      @*/
    /*@
    model public JMLListEqualsNode removePrefix(\bigint n) {
        return (n <= 0 
                ? this
                : (next == null ? null : next.removePrefix(n-1))
                );
    }
    @*/

    /** Return a list containing all but the first n elements in this list.
     *  @param n the number of elements to remove
     *  @return null if n is negative or greater than the length of this list.
     */
    /*@  public normal_behavior
      @  {|
      @     requires 0 < n && n < int_length();
      @     ensures \result != null
      @          && \result.int_length() == int_length() - n
      @          && (\forall int i; n <= i && i < int_length();
      @                             \result.itemAt((int)(i-n)) == itemAt(i));
      @   also
      @     requires n <= 0;
      @     ensures this.equals(\result);
      @   also
      @     requires int_length() <= n;
      @     ensures \result == null;
      @  |}
      @
      @ implies_that
      @    ensures !containsNull && \result != null ==> !\result.containsNull;
      @*/
    public JMLListEqualsNode removePrefix(int n) {
        return (n <= 0 
                ? this
                : (next == null ? null : next.removePrefix(n-1))
                );
    }

    /** Return a list like this list, but without the element at the
     *  given zero-based index.
     *  @param n the zero-based index into the list.
     *  @return null if the index is out of range or if the list was of size 1.
     */
    /*@  public normal_behavior
      @    requires n == 0 && length() == 1;
      @    ensures \result == null;
      @ also
      @   public normal_behavior
      @    requires n == 0 && length() > 1;
      @    ensures \result.equals(removePrefix(1));
      @ also
      @   public normal_behavior
      @    requires 0 < n && n < length();
      @    ensures \result != null
      @         && \result.length() == length() - 1
      @         && \result.equals(prefix(n).concat(removePrefix(n+1)));
      @ // !FIXME! This spec is inconsistent. Take n == length() - 1.
      @ // then removePrefix(n+1) --> removePrefix(length()) --> null.
      @ // But concat requires non_null.  Maybe spec of concat should be relaxed?
      @
      @ implies_that
      @    ensures !containsNull && \result != null ==> !\result.containsNull;
      @*/
    /*@
    model public JMLListEqualsNode removeItemAt(\bigint n) {
        return (n <= 0 
                ? next
                : (next == null ? null 
                   : new JMLListEqualsNode(val, next.removeItemAt(n-1)))
                );
    }
    @*/

    /** Return a list like this list, but without the element at the
     *  given zero-based index.
     *  @param n the zero-based index into the list.
     *  @return null if the index is out of range or if the list was of size 1.
     */
    /*@  public normal_behavior
      @    requires n == 0 && int_length() == 1;
      @    ensures \result == null;
      @ also
      @   public normal_behavior
      @    requires n == 0 && int_length() > 1;
      @    ensures \result.equals(removePrefix(1));
      @ also
      @   public normal_behavior
      @    requires 0 < n && n < int_length();
      @    ensures \result != null
      @         && \result.int_length() == int_length() - 1
      @         && \result.equals(prefix(n).concat(removePrefix((int)(n+1))));
      @ // !FIXME! This spec is inconsistent. Take n == int_length() - 1.
      @ // then removePrefix((int)(n+1)) --> removePrefix(int_length()) --> null.
      @ // But concat requires non_null.  Maybe spec of concat should be relaxed?
      @
      @ implies_that
      @    ensures !containsNull && \result != null ==> !\result.containsNull;
      @*/
    public JMLListEqualsNode removeItemAt(int n) {
        return (n <= 0 
                ? next
                : (next == null ? null 
                   : new JMLListEqualsNode(val, next.removeItemAt(n-1)))
                );
    }

    /** Return a list like this, but with item replacing the element at the
     *  given zero-based index.
     *  @param n the zero-based index into this list.
     *  @param item the item to put at index index
     */
    /*@  public normal_behavior
      @    requires 0 <= n && n < length();
      @    ensures \result != null && \result.length() == length();
      @ also
      @   public normal_behavior
      @    requires n == 0 && length() == 1;
      @    ensures \result != null
      @         && \result.equals(cons(item, next));
      @ also
      @   public normal_behavior
      @    requires n == 0 && length() > 1;
      @    ensures \result != null
      @         && \result.equals(removePrefix(1).prepend(item));
      @ also
      @   public normal_behavior
      @    requires 0 < n && n == length()-1;
      @    ensures \result != null 
      @         && \result.equals(prefix(n).append(item));
      @ also
      @   public normal_behavior
      @    requires 0 < n && n < length()-1;
      @    ensures \result != null && \result.length() == length()
      @         && \result.equals(prefix(n)
      @                           .concat(removePrefix(n+1).prepend(item)));
      @ implies_that
      @    requires 0 <= n;
      @    ensures n == 0 ==> \result != null;
      @    ensures item == null && \result != null ==> \result.containsNull;
      @    ensures item != null && !containsNull && \result != null
      @            ==> !\result.containsNull;
      @*/
    /*@
    model public JMLListEqualsNode replaceItemAt(\bigint n, Object item) {
        return (n <= 0 
                ? cons(item, next) // cons() handles any necessary cloning
                : (next == null ? null 
                   : new JMLListEqualsNode(val, 
                                           next.replaceItemAt(n-1, item)))
                );
    }  nowarn Post;
    @*/

    /** Return a list like this, but with item replacing the element at the
     *  given zero-based index.
     *  @param n the zero-based index into this list.
     *  @param item the item to put at index index
     */
    /*@  public normal_behavior
      @    requires 0 <= n && n < int_length();
      @    ensures \result != null && \result.int_length() == int_length();
      @ also
      @   public normal_behavior
      @    requires n == 0 && int_length() == 1;
      @    ensures \result != null
      @         && \result.equals(cons(item, next));
      @ also
      @   public normal_behavior
      @    requires n == 0 && int_length() > 1;
      @    ensures \result != null
      @         && \result.equals(removePrefix(1).prepend(item));
      @ also
      @   public normal_behavior
      @    requires 0 < n && n == int_length()-1;
      @    ensures \result != null 
      @         && \result.equals(prefix(n).append(item));
      @ also
      @   public normal_behavior
      @    requires 0 < n && n < int_length()-1;
      @    ensures \result != null && \result.int_length() == int_length()
      @         && \result.equals(prefix(n)
      @                           .concat(removePrefix(n+1).prepend(item)));
      @ implies_that
      @    requires 0 <= n;
      @    ensures n == 0 ==> \result != null;
      @    ensures item == null && \result != null ==> \result.containsNull;
      @    ensures item != null && !containsNull && \result != null
      @            ==> !\result.containsNull;
      @*/
    public JMLListEqualsNode replaceItemAt(int n, Object item) {
        return (n <= 0 
                ? cons(item, next) // cons() handles any necessary cloning
                : (next == null ? null 
                   : new JMLListEqualsNode(val, 
                                           next.replaceItemAt(n-1, item)))
                );
    } //@ nowarn Post;

    /** Return a list containing all but the last element in this.
     */
    /*@  public normal_behavior // !FIXME! inconsistent spec [when int_length() == 1]
      @    ensures \result == null ==> int_length() == 1;
      @    ensures \result != null ==> \result.equals(prefix((int)(int_length() - 1)));
      @ implies_that
      @    ensures !containsNull && \result != null ==> !\result.containsNull;
      @*/
    public JMLListEqualsNode removeLast() {
        return (next == null 
                ? null 
                : new JMLListEqualsNode(val, next.removeLast()));
    }

    /** Return a list that is the concatenation of this with the given
     *  lists.
     *  @param ls2 the list to place at the end of this list in the
     *  result.
     *  @return the concatenation of this list and ls2.
     */
    /*@  public normal_behavior
      @    requires ls2 != null;
      @    ensures \result != null
      @         && \result.int_length() == int_length() + ls2.int_length()
      @         && (\forall int i; 0 <= i && i < int_length();
      @                           \result.itemAt(i) == itemAt(i))
      @         && (\forall int i; 0 <= i && i < ls2.int_length();
      @                           \result.itemAt((int)(int_length()+i)) == ls2.itemAt(i));
      @    ensures (* \result is the concatenation of this followed by ls2 *);
      @*/
    public /*@ non_null @*/
        JMLListEqualsNode concat(/*@ non_null @*/ JMLListEqualsNode ls2)
    {
        return (next == null
                ? new JMLListEqualsNode(val, ls2)
                : new JMLListEqualsNode(val, next.concat(ls2))
                );
    }

    /** Return a list that is like this, but with the given item at
     *  the front. Note that this clones the item if necessary.
     *  @param item the element to place at the front of the result.
     */
    /*@  public normal_behavior
      @    ensures \result != null && \result.equals(cons(item, this));
      @    ensures_redundantly \result != null
      @         && \result.int_length() == int_length() + 1;
      @*/
    public /*@ non_null @*/ JMLListEqualsNode prepend(Object item) {
        // cons() handles any necessary cloning
        return cons(item, this);
    }

    /** Return a list that consists of this list and the given element.
     */
    /*@  public normal_behavior
      @    ensures \result != null
      @         && \result.equals(cons(item, this.reverse()).reverse());
      @    ensures_redundantly \result != null
      @         && \result.int_length() == int_length() + 1;
      @*/
    public /*@ non_null @*/ JMLListEqualsNode append(Object item) {
        // To avoid full recursion, we build the reverse of what we want in
        // revret, then reverse it.  To make sure we only clone once,
        // we let reverse do the cloning
        JMLListEqualsNode ptr = this;
        JMLListEqualsNode revret = null;
        //@ maintaining (* reverse(revret) concatenated with ptr equals this *);
        while (ptr != null) {
            revret = new JMLListEqualsNode(ptr.val, revret); // don't clone yet
            ptr = ptr.next;
        }
        return (new JMLListEqualsNode(item, revret)).reverse();
    }

    /** Return a list that is the reverse of this list.
     */
    /*@  public normal_behavior
      @    ensures \result.int_length() == int_length()
      @      && (\forall int i; 0 <= i && i < int_length();
      @           (\result.itemAt((int)(int_length()-i-1)) != null 
      @            && \result.itemAt((int)(int_length()-i-1)).equals(itemAt(i)))
      @          || (\result.itemAt((int)(int_length()-i-1)) == null
      @              && itemAt(i) == null) );
      @    ensures_redundantly
      @            (* \result has the same elements but with the items 
      @               arranged in the reverse order *);
      @
      @ implies_that
      @    ensures elementType == \result.elementType;
      @    ensures containsNull <==> \result.containsNull;
      @*/
    public /*@ non_null @*/ JMLListEqualsNode reverse() {
        JMLListEqualsNode ptr = this;
        JMLListEqualsNode ret = null;
        //@ loop_invariant ptr != this ==> ret != null;
        //@ maintaining (* ret is the reverse of items in this up to ptr *);
        while (ptr != null) {
            //@ assume ptr.val != null ==> \typeof(ptr.val) <: elementType;
            ret = new JMLListEqualsNode(ptr.val == null ? null
                                        : (Object)(ptr.val) ,
                                        ret);
            ptr = ptr.next;
        }
        //@ assert ptr == null && ret != null;
        //@ assume elementType == ret.elementType;
        //@ assume containsNull <==> ret.containsNull;
        return ret;
    }

    /** Return a list that is like this list but with the given item
     * inserted before the given index.
     */
    /*@  public normal_behavior
      @    requires 0 < n && n <= length();
      @    ensures \result != null
      @       && \result.equals(prefix(n).concat(cons(item, removePrefix(n))));
      @ also
      @   public normal_behavior
      @    requires n == 0;
      @    ensures \result != null && \result.equals(cons(item, this));
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length());
      @    signals_only JMLListException;
      @*/
    /*@
    model public  non_null 
        JMLListEqualsNode insertBefore(\bigint n, Object item) 
        throws JMLListException {
        if ( n < 0 || (n > 1 && next == null) ) {
            throw new JMLListException("Index to insertBefore out of range.");
        } else if (n == 0) {
            return cons(item, this); // cons() handles any necessary cloning
        } else {
             assert n > 0;
            return new JMLListEqualsNode(val,
                                         (next == null
                                          ? cons(item, null)
                                          : next.insertBefore(n-1, item)));
        }
    }
    @*/

    /** Return a list that is like this list but with the given item
     * inserted before the given index.
     */
    /*@  public normal_behavior
      @    requires 0 < n && n <= int_length();
      @    ensures \result != null
      @       && \result.equals(prefix(n).concat(cons(item, removePrefix(n))));
      @ also
      @   public normal_behavior
      @    requires n == 0;
      @    ensures \result != null && \result.equals(cons(item, this));
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= int_length());
      @    signals_only JMLListException;
      @*/
    public /*@ non_null @*/
        JMLListEqualsNode insertBefore(int n, Object item) 
        throws JMLListException {
        if ( n < 0 || (n > 1 && next == null) ) {
            throw new JMLListException("Index to insertBefore out of range.");
        } else if (n == 0) {
            return cons(item, this); // cons() handles any necessary cloning
        } else {
            //@ assert n > 0;
            return new JMLListEqualsNode(val,
                                         (next == null
                                          ? cons(item, null)
                                          : next.insertBefore(n-1, item)));
        }
    }

    /** Return a list that is like this list but without the first
     * occurrence of the given item.
     */
    /*@  public normal_behavior
      @    requires !has(item);
      @    ensures this.equals(\result);
      @ also
      @  public normal_behavior
      @    old int index = indexOf(item);
      @    requires has(item);
      @    ensures \result == null <==> \old(int_size() == 1);
      @    ensures \result != null && index == 0
      @        ==> \result.equals(removePrefix(1));
      @    ensures \result != null && index > 0 // !FIXME! [? index == int_length() - 1]
      @        ==> \result.equals(prefix(index).concat(removePrefix((int)(index+1))));
      @*/
    public JMLListEqualsNode remove(Object item) {
        if ((item == null && val == null) || item.equals(val)) return next;
        return new JMLListEqualsNode(val,
                                             (next == null ? null
                                              : next.remove(item)));
    }

    /** Return a string representation for this list.  The output is ML style.
     */
    public /*@ non_null @*/ String toString() {
        String ret = "[";
        JMLListEqualsNode thisLst = this;
        boolean firstTime = true;
        while (thisLst != null) {
            if (!firstTime) {
                ret += ", ";
            } else {
                firstTime = false;
            }
            if (thisLst.val == null) {
                ret += "null";
            } else {
                ret += thisLst.val.toString();
            }
            thisLst = thisLst.next;
        }
        ret += "]";
        return ret;
    }

}
