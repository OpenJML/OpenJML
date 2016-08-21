package org.jmlspecs.genericmodels;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.Pure;

/*@ pure spec_public @*/ abstract class JMLListNode<E> implements JMLType {
    
    private static final long serialVersionUID = 1L;
    
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
      @    // of the other methods is defined based by these two 
      @    // methods.
      @ 
      @    ensures \result <==>
      @        cons(e1, null).size() == 1;
      @  also
      @    ensures \result <==>
      @        (ls != null)
      @          ==> cons(e1, ls).size() == 1 + ls.size();
      @  also
      @    ensures \result <==>
      @        (ls != null)
      @          ==> (ls.next() == null) == (ls.size() == 1);
      @  also
      @    ensures \result <==>
      @        ls != null && ls.next() != null 
      @          ==> ls.size() == 1 + ls.next().size();
      @  also
      @    ensures \result <==>
      @        (ls != null && ls.val() != null)
      @          ==> elem_equals(ls.val(),ls.head());
      @  also
      @    ensures \result <==>
      @        (e1 != null)
      @          ==> elem_equals(cons(e1, ls).head(),e1);
      @  also
      @    ensures \result <==>
      @        (ls != null && ls.val() != null)
      @          ==> elem_equals(ls.itemAt(0),ls.head());
      @  also
      @    ensures \result <==>
      @        ls != null && 0 < n && n < ls.size()
      @          ==> elem_equals(ls.itemAt(n),ls.next().itemAt(n - 1));
      @ |}
      public pure model boolean equational_theory(
                 @Nullable JMLListNode<E> ls, @Nullable JMLListNode<E> ls2,
                       @Nullable E e1, @Nullable E e2, \bigint n);
      @*/

    //@ public model JMLDataGroup elementState;

    /** The data contained in this list node.
     */
    public final @Nullable E val;
    //@ in objectState; maps val.objectState \into elementState;

    protected JMLListNode(E item) {
        val = item;
    }
    
    /** The next node in this list.
     */
    public abstract @Nullable JMLListNode<E> next();

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
    //@ public invariant next() != null ==> next().elementType <: elementType;

    /** Whether this list can contain null elements;
     */
    //@ ghost public boolean containsNull;

    //@ public constraint containsNull == \old(containsNull);

    //@ public invariant containsNull <==> has(null);

    /*@ protected
      @    invariant containsNull <==>
      @              val == null || (next() != null && next().containsNull);
      @*/

    //@ public invariant owner == null;
    
    //@ ensures ( e == o ) ==> \result;
    public abstract boolean elem_equals(@Nullable E e, @Nullable Object o);
    

    /** Return a JMLListNode containing the given element
     *  followed by the given list.
     *
     * Note that cons() adds elements to the front of a list.  
     * It handles any necessary cloning for value lists and it handles 
     * inserting null elements.
     *
     * @param hd the object to place at the head of the result.
     * @param tl the JMLListNode to make the tail of the result.
     */
    // This is not static even though it does not use this, because we want to override it
    /*@  public normal_behavior
      @    ensures \result.headEquals(hd) && \result.next() == tl;
      @    ensures \result.equals(new JMLListEqualsNode(hd, tl));
      @
      @ implies_that public normal_behavior
      @    ensures \result != null
      @         && \result.containsNull <==>
      @             hd == null || (tl != null && tl.containsNull);
      @*/
    public @Pure @NonNull JMLListNode<E> cons(@Nullable E hd, @Nullable JMLListNode<E> tl) {
        return tl == null ? singleton(hd) : tl.prepend(hd);
    }

    public abstract @Pure @NonNull JMLListNode<E> singleton(@Nullable E hd);
    
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
        return val;
    }

    /** Tell if the head of the list is equal to the given
     * item.
     * @see #has(Object)
     */
    /*@  public normal_behavior
      @    ensures \result == elem_equals(val,item);
      @*/
    public boolean headEquals(@Nullable Object item) {
        return elem_equals(val, item);
    }

    /** Return the ith element of a list.
     * @see #getItem(\bigint)
     */
    /*@  public normal_behavior
      @    requires 0 <= i && i < length();
      @    ensures \result != null ==>
      @                (* \result ".equals" the ith element of this *);
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
            @Nullable JMLListEqualsNode<E> ptr = this;
              maintaining k >= 0;
              decreasing k;
            while (ptr != null && k > 0) {
                k = k - 1;
                ptr = ptr.next();
            }
            if (ptr == null) {
                throw new JMLListException("Index to itemAt(\bigint) out of range.");
            } else {
                  assert ptr != null && k == 0;
                  assume ptr.val != null
                          ==> \typeof(ptr.val) <: \type(E);
                  
                @Nullable E ret = ptr.val;
                  assume ret != null ==> \typeof(ret) <: elementType;
                  assume !containsNull ==> ret != null;
                return ret;
            }
        }
    }
    @*/

    /** Return the ith element of a list.
     * @see #getItem(int)
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
    public @Nullable E itemAt(int i) throws JMLListException {
        if (i < 0) {
            throw new JMLListException("Index to itemAt(int) is negative "
                                       + i);
        } else {
            int k = i;
            //@ assert k >= 0;
            @Nullable JMLListNode<E> ptr = this;
            //@ maintaining k >= 0;
            //@ decreasing k;
            while (ptr != null && k > 0) {
                k--;
                ptr = ptr.next();
            }
            if (ptr == null) {
                throw new JMLListException("Index to itemAt(int) out of range.");
            } else {
                //@ assert ptr != null && k == 0;
                /*@ assume ptr.val != null
                  @        ==> \typeof(ptr.val) <: \type(Object);
                  @*/
                @Nullable E ret = ptr.val;
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
          @NonNull JMLListEqualsNode<E> ptr = this;
          maintaining (* ptr is count next()'s from this *);
          while (ptr != null) {
            ptr = ptr.next();
            count = count + 1;
          }
          return count;
      @ } 
      @*/

    /** Tells the number of elements in the sequence; a synonym for size
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
        @Nullable JMLListNode<E> ptr = this;
        //@ maintaining (* ptr is count next's from this *);
        while (ptr != null) {
            ptr = ptr.next();
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
        @Nullable JMLListNode<E> ptr = this;
        //@ maintaining (* no earlier element is elem_equals to item *);
        while (ptr != null) {
            if (elem_equals(ptr.val, item)) {
                return true;
            }
            ptr = ptr.next();
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
    public boolean isPrefixOf(@Nullable JMLListNode<E> ls2) {
        if (ls2 == null) {
            return false;
        }
        JMLListNode<E> othLst = ls2;
        JMLListNode<E> thisLst = this;
        /*@ maintaining
          @ (* all earlier elements of both lists are elem_equals *);
          @*/
        while (thisLst != null && othLst != null) {
            if (!elem_equals(thisLst.val, othLst.val)) {
                return false;
            }
            thisLst = thisLst.next();
            othLst = othLst.next();
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
    public boolean equals(@Nullable Object ls2) {
        if (ls2 != null && ls2 instanceof JMLListNode) {
            @Nullable JMLListNode<E> othLst = (JMLListNode<E>)ls2;
            return equals(this,othLst);
        } else {
            return false;
        }
    }
    
    protected boolean equals(@Nullable JMLListNode<E> ls, @Nullable JMLListNode<E> ls2) {
        if (ls == ls2) return true;
        if (ls == null) return false;
        return elem_equals(ls.val,ls2.val) && equals(ls.next(),ls2.next());
    }

    /** Return a hash code for this object.
     */
    public int hashCode() {
        int hash = 0;
        @Nullable JMLListNode<E> ptr = this;
        while (ptr != null) {
            @Nullable Object v = ptr.val;
            if (v != null) {
                hash += v.hashCode();
            }
            ptr = ptr.next();
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
        @Nullable JMLListNode<E> ptr = this;
        maintaining (* ptr is idx next's from this *);
        while (ptr != null) {
            if (elem_equals(ptr.val, item)) {
                return idx;
            }
            ptr = ptr.next();
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
      @    requires has(item);
      @    ensures elem_equals(itemAt(\result),item)
      @          && (\forall int i; 0 <= i && i < \result;
      @                             !(itemAt(i) != null
      @                               && elem_equals(itemAt(i),item)));
      @    ensures_redundantly
      @          (* \result is the first index at which item occurs in this *);
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
        @Nullable JMLListNode<E> ptr = this;
        //@ maintaining (* ptr is idx next's from this *);
        while (ptr != null) {
            if (elem_equals(ptr.val, item)) {
                return idx;
            }
            ptr = ptr.next();
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
    public @Nullable E last() {
        @Nullable JMLListNode<E> ptr = this;
        //@ maintaining ptr != null;
        while (ptr.next() != null) {
            ptr = ptr.next();
        }
        //@ assert ptr.next() == null;
        //@ assume ptr.val != null ==> \typeof(ptr.val) <: \type(E);
        //@ assume !containsNull ==> ptr.val != null;
        return ptr.val;
    }

    /** Return the first occurrence of the given
     *  element in the list, if there is one
     *  @param item the Object sought in this list.
     *  @return the first item equal to the argument.
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
    public @Nullable E getItem(@Nullable Object item) throws JMLListException {
        @Nullable JMLListNode<E> ptr = this;
        //@ maintaining (* no earlier element is elem_equals to item *);
        while (ptr != null) {
            if (elem_equals(ptr.val, item)) {
                //@ assume ptr.val != null ==> \typeof(ptr.val) <: elementType;
                return ptr.val;
            }
            ptr = ptr.next();
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
    model public @Nullable JMLListNode<E> prefix(\bigint n) {
        return (n <= 0 
                ? null 
                : new JMLListEqualsNode<E>(val, 
                                        (next() == null ? null 
                                         : next().prefix(n-1)))
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
    public @Nullable JMLListNode<E> prefix(int n) {
        return (n <= 0 
                ? null 
                : cons(val, (next() == null ? null 
                                         : next().prefix(n-1)))
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
    model public @Nullable JMLListNode<E> removePrefix(\bigint n) {
        return (n <= 0 
                ? this
                : (next() == null ? null : next().removePrefix(n-1))
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
    public @Nullable JMLListNode<E> removePrefix(int n) {
        return (n <= 0 
                ? this
                : (next() == null ? null : next().removePrefix(n-1))
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
    model public @Nullable JMLListNode<E> removeItemAt(\bigint n) {
        return (n <= 0 
                ? next()
                : next() == null ? null : cons(val, next().removeItemAt(n-1)))
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
    public @Nullable JMLListNode<E> removeItemAt(int n) {
        return (n <= 0 
                ? next()
                : (next() == null ? null 
                   : cons(val, next().removeItemAt(n-1)))
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
      @         && \result.equals(cons(item, next()));
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
    model public @NonNull JMLListNode<E> replaceItemAt(\bigint n, E item) {
        return (n <= 0 
                ? cons(item, next()) // cons() handles any necessary cloning
                : (next() == null ? null 
                   : cons(val,next().replaceItemAt(n-1, item)))
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
      @         && \result.equals(cons(item, next()));
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
    public @NonNull JMLListNode<E> replaceItemAt(int n, @Nullable E item) {
        return (n <= 0 
                ? cons(item, next()) // cons() handles any necessary cloning
                : (next() == null ? null 
                   : cons(val,next().replaceItemAt(n-1, item)))
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
    public @Nullable JMLListNode<E> removeLast() {
        return (next() == null 
                ? null 
                : cons(val, next().removeLast()));
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
        JMLListNode<E> concat(@Nullable JMLListNode<E> ls2)
    {
        return (next() == null
                ? cons(val, ls2)
                : cons(val, next().concat(ls2))
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
    public @NonNull JMLListNode<E> prepend(@Nullable E item) {
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
    public @NonNull JMLListNode<E> append(@Nullable E item) {
        // To avoid full recursion, we build the reverse of what we want in
        // revret, then reverse it.  To make sure we only clone once,
        // we let reverse do the cloning
        @NonNull JMLListNode<E> ptr = this;
        @Nullable JMLListNode<E> revret = null;
        //@ maintaining (* reverse(revret) concatenated with ptr equals this *);
        while (ptr != null) {
            revret = cons(ptr.val, revret); // don't clone yet
            ptr = ptr.next();
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
    public @NonNull JMLListNode<E> reverse() {
        @Nullable JMLListNode<E> ptr = this;
        @Nullable JMLListNode<E> ret = null;
        //@ loop_invariant ptr != this ==> ret != null;
        //@ maintaining (* ret is the reverse of items in this up to ptr *);
        while (ptr != null) {
            //@ assume ptr.val != null ==> \typeof(ptr.val) <: elementType;
            ret = cons(ptr.val,ret);
            ptr = ptr.next();
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
        if ( n < 0 || (n > 1 && next() == null) ) {
            throw new JMLListException("Index to insertBefore out of range.");
        } else if (n == 0) {
            return cons(item, this); // cons() handles any necessary cloning
        } else {
             assert n > 0;
            return new JMLListEqualsNode(val,
                                         (next() == null
                                          ? cons(item, null)
                                          : next().insertBefore(n-1, item)));
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
        JMLListNode<E> insertBefore(int n, @Nullable E item) 
        throws JMLListException {
        if ( n < 0 || (n > 1 && next() == null) ) {
            throw new JMLListException("Index to insertBefore out of range.");
        } else if (n == 0) {
            return cons(item, this); // cons() handles any necessary cloning
        } else {
            //@ assert n > 0;
            return cons(val,
                                         (next() == null
                                          ? cons(item, null)
                                          : next().insertBefore(n-1, item)));
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
    public @Nullable JMLListNode<E> remove(@Nullable Object item) {
        if (elem_equals(val,item)) {
            return next();
        } else {
            return cons(val,
                                         (next() == null ? null
                                          : next().remove(item)));
        }
    }

    /** Return a string representation for this list.  The output is ML style.
     */
    public @NonNull String toString() {
        String ret = "[";
        @Nullable JMLListNode<E> thisLst = this;
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
            thisLst = thisLst.next();
        }
        ret += "]";
        return ret;
    }

}
