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


package org.jmlspecs.unfinished;
import org.jmlspecs.annotation.*;

/** An implementation class used in various models.  These are
 * singly-linked list nodes containing objects.  The empty
 * list is represented by null, which makes dealing with these lists
 * tricky.  Normal users should use {@link JMLEqualsSequence} instead of this
 * type to avoid these difficulties.  Nodes can contain null values.
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
/*@ pure spec_public @*/ class JMLListEqualsNode<E> extends JMLListNode<E> implements JMLType {

    private static final long serialVersionUID = 626734542482855323L;
    
    @Override
    public boolean elem_equals(@Nullable E e, @Nullable Object o) {
        return e == o || (e != null && e.equals(o));
    }
    
//    /** Return a JMLListEqualsNode containing the given element
//     *  followed by the given list.
//     *
//     * Note that cons() adds elements to the front of a list.  
//     * It handles any necessary cloning for value lists and it handles 
//     * inserting null elements.
//     *
//     * @param hd the object to place at the head of the result.
//     * @param tl the JMLListEqualsNode to make the tail of the result.
//     */
//    /*@  public normal_behavior
//      @    ensures \result.headEquals(hd) && \result.next == tl;
//      @    ensures \result.equals(new JMLListEqualsNode(hd, tl));
//      @
//      @ implies_that public normal_behavior
//      @    ensures \result != null
//      @         && \result.containsNull <==>
//      @             hd == null || (tl != null && tl.containsNull);
//      @*/
    public @NonNull JMLListEqualsNode<E> cons(E item, JMLListEqualsNode<E> tail) {
        return new JMLListEqualsNode<E>(item,(JMLListEqualsNode<E>)tail);
    }
    
    public @NonNull JMLListEqualsNode<E> singleton(E item) {
        return new JMLListEqualsNode<E>(item,null);
    }

    //*********************** equational theory ***********************

    /*@ public invariant (\forall @Nullable JMLListEqualsNode l2;
      @                    (\forall @Nullable E e1, e2;
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
      @       (new JMLListEqualsNode<E>(e1, null)).size() == 1;
      @  also
      @    ensures \result <==>
      @        (ls != null)
      @          ==> (new JMLListEqualsNode<E>(e1, ls)).size() == 1 + ls.size();
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
                       @Nullable JMLListEqualsNode<E> ls, @Nullable JMLListEqualsNode<E> ls2,
                       @Nullable E e1, @Nullable E e2, \bigint n);
      @*/

    //@ public model JMLDataGroup elementState;

//    /** The data contained in this list node.
//     */
//    public final @Nullable E val;
//    //@ in objectState; maps val.objectState \into elementState;

    /** The next node in this list.
     */
    public final @Nullable JMLListEqualsNode<E> next;
    //@ in objectState; maps next.elementState \into elementState;

    public @Nullable JMLListEqualsNode<E> next() { return next; }

    /** The type of the elements in this list.  This type is an upper
     * bound on the element's types. The type is computed
     * pessimistically, so that the order of adding elements does not
     * matter; that is, if any element in the list is null, then we
     * use Object as the type of the list's elements.
     */
    //@ ghost @NonNull public \TYPE elementType;

    //@ public constraint elementType == \old(elementType);

    //@ public invariant elementType <: \type(E);

    //@ public invariant val != null ==> \typeof(val) <: elementType;
    //@ public invariant val == null ==> \type(E) == elementType;
    /*@ public invariant_redundantly
      @         containsNull ==> \type(E) == elementType;
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
    public JMLListEqualsNode(E item, JMLListEqualsNode<E> nxt) {
        super(item);
        //@ set owner = null;
        next = nxt;
        /*@ set elementType
          @     = (item == null 
          @         ? \type(E)
          @         : (nxt == null ? \typeof(item)
          @                        : ((\typeof(item) <: nxt.elementType)
          @                            ? nxt.elementType
          @                            // types aren't totally ordered!
          @                            : ((nxt.elementType <: \typeof(item))
          @                               ? \typeof(item)
          @                               : \type(E)))));
          @*/
        /*@ set containsNull
          @       = (val == null || (next != null && next.containsNull));
          @*/
    } //@ nowarn Invariant;

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
    public @Nullable E head() {
        E ret = val;
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
      model public @Nullable E itemAt(\bigint i) throws JMLListException {
        if (i < 0) {
            throw new JMLListException("Index to itemAt(int) is negative "
                                       + i);
        } else {
            \bigint k = i;
              assert k >= 0;
            JMLListEqualsNode<E> ptr = this;
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
                          ==> \typeof(ptr.val) <: \type(E);
                  
                E ret = ptr.val;
                  assume ret != null ==> \typeof(ret) <: elementType;
                  assume !containsNull ==> ret != null;
                return ret;
            }
        }
    }
    @*/



    // ******************** building new JMLEqualsLists ***********************
             
    /** Return a clone of this object.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result != null && \result instanceof JMLListEqualsNode
      @            && ((JMLListEqualsNode)\result).equals(this);
      @*/
    public @NonNull Object clone() {
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
    model public JMLListEqualsNode<E> prefix(\bigint n) {
        return (n <= 0 
                ? null 
                : cons(val, 
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
    public @Nullable JMLListEqualsNode<E> prefix(int n) {
        return (n <= 0 
                ? null 
                : cons(val, 
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
    model public @Nullable JMLListEqualsNode<E> removePrefix(\bigint n) {
        return (n <= 0 
                ? this
                : (next == null ? null : next.removePrefix(n-1))
                );
    }
    @*/

    /** Return a list containing all but the first n elements in this list.
     *  @param n the number of elements to remove
     *  @return this if n is negative, null if n is greater than the length of this list.
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
    public JMLListEqualsNode<E> removePrefix(int n) {
        return (n <= 0 
                ? this
                : (next == null ? null : next.removePrefix(n-1))
                );
    }

    /** Return a list like this list, but without the element at the
     *  given zero-based index.
     *  @param n the zero-based index into the list.
     *  @return list with one less element
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
      @
      @ implies_that
      @    ensures !containsNull && \result != null ==> !\result.containsNull;
      @*/
    /*@
    model public JMLListEqualsNode<E> removeItemAt(\bigint n) {
        return (n <= 0 
                ? next
                : (next == null ? null 
                   : cons(val, next.removeItemAt(n-1)))
                );
    }
    @*/

    /** Return a list like this list, but without the element at the
     *  given zero-based index.
     *  @param n the zero-based index into the list.
     *  @return a list with one less element
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
      @
      @ implies_that
      @    ensures !containsNull && \result != null ==> !\result.containsNull;
      @*/
    public @Nullable JMLListEqualsNode<E> removeItemAt(int n) {
        return (n <= 0 
                ? next
                : (next == null ? null 
                   : cons(val, next.removeItemAt(n-1)))
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
    model public JMLListEqualsNode<E> replaceItemAt(\bigint n, E item) {
        return (n <= 0 
                ? cons(item, next) // cons() handles any necessary cloning
                : (next == null ? null 
                   : cons(val, next.replaceItemAt(n-1, item)))
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
    public JMLListEqualsNode<E> replaceItemAt(int n, E item) {
        return (n <= 0 
                ? cons(item, next) // cons() handles any necessary cloning
                : (next == null ? null 
                   : cons(val, next.replaceItemAt(n-1, item)))
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
    public @Nullable JMLListEqualsNode<E> removeLast() {
        return (next == null 
                ? null 
                : cons(val, next.removeLast()));
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
    public @NonNull
        JMLListEqualsNode<E> concat(@Nullable JMLListEqualsNode<E> ls2)
    {
        return (next == null
                ? cons(val, ls2)
                : cons(val, next.concat(ls2))
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
    public @NonNull JMLListEqualsNode<E> prepend(@Nullable E item) {
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
    public @NonNull JMLListEqualsNode<E> append(@Nullable E item) {
        // To avoid full recursion, we build the reverse of what we want in
        // revret, then reverse it.  To make sure we only clone once,
        // we let reverse do the cloning
        @NonNull JMLListEqualsNode<E> ptr = this;
        @Nullable JMLListEqualsNode<E> revret = null;
        //@ maintaining (* reverse(revret) concatenated with ptr equals this *);
        while (ptr != null) {
            revret = new JMLListEqualsNode<E>(ptr.val, revret); // don't clone yet
            ptr = ptr.next;
        }
        return (cons(item, revret)).reverse();
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
    public @NonNull JMLListEqualsNode<E> reverse() {
        @Nullable JMLListEqualsNode<E> ptr = this;
        @Nullable JMLListEqualsNode<E> ret = null;
        //@ loop_invariant ptr != this ==> ret != null;
        //@ maintaining (* ret is the reverse of items in this up to ptr *);
        while (ptr != null) {
            //@ assume ptr.val != null ==> \typeof(ptr.val) <: elementType;
            ret = cons(ptr.val,ret);
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
      @*/
    /*@
    model public @NonNull 
        JMLListEqualsNode<E> insertBefore(\bigint n, E item) 
        throws JMLListException {
        if ( n < 0 || (n > 1 && next == null) ) {
            throw new JMLListException("Index to insertBefore out of range.");
        } else if (n == 0) {
            return cons(item, this); // cons() handles any necessary cloning
        } else {
             assert n > 0;
            return cons(val,
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
    public @NonNull
        JMLListEqualsNode<E> insertBefore(int n, @Nullable E item) 
        throws JMLListException {
        if ( n < 0 || (n > 1 && next == null) ) {
            throw new JMLListException("Index to insertBefore out of range.");
        } else if (n == 0) {
            return cons(item, this); // cons() handles any necessary cloning
        } else {
            //@ assert n > 0;
            return cons(val,
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
    public @Nullable JMLListEqualsNode<E> remove(@Nullable Object item) {
        if (elem_equals(val,item)) {
            return next;
        } else {
            return cons(val,
                                         (next == null ? null
                                          : next.remove(item)));
        }
    }



}
