// @(#)$Id: JMLSequence.java-generic,v 1.80 2006/12/24 22:35:54 leavens Exp $

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
import java.math.BigInteger;

import org.jmlspecs.lang.JMLIterator;

/** Sequences of values.  This type uses ".equals"
 * to compare elements, and clones elements that are passed into
 * and returned from the sequence's methods.
 *
 * <p> The informal model for a JMLValueSequence is a finite
 * mathematical sequence of elements (of type {@link JMLType}). In
 * some examples, we will write
 * &lt;<em>a</em>,<em>b</em>,<em>c</em>&gt; for a mathematical
 * sequence of length 3, containing elements <em>a</em>, <em>b</em>,
 * and <em>c</em>. Elements of sequences are "indexed" from 0, so the
 * length of a sequence is always 1 more than the index of the last
 * element in the sequence.
 *
 * @version $Revision: 1.80 $
 * @author Gary T. Leavens
 * @author Albert L. Baker
 * @see JMLCollection
 * @see JMLType
 * @see JMLObjectSequence
 * @see JMLValueSequenceEnumerator
 * @see JMLValueSequenceSpecs
 */
//+OPENJML@ immutable
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public /*@ pure @*/ class JMLValueSequence
    extends JMLValueSequenceSpecs implements JMLCollection
{

    //*********************** equational theory ***********************

    /*@ public invariant (\forall JMLValueSequence s2;
      @                    (\forall JMLType e1, e2;
      @                     (\forall \bigint n;
      @                       equational_theory(this, s2, e1, e2, n) )));
      @*/

    /** An equational specification of the properties of sequences.
     */
    /*@ public normal_behavior
      @ {|
      @  // The following are defined by observations (itemAt) and induction.
      @ 
      @    ensures \result <==> !(new JMLValueSequence()).has(e1);
      @  also
      @    ensures \result <==> (new JMLValueSequence()).size() == 0;
      @  also
      @    ensures \result <==> (new JMLValueSequence(e1)).size() == 1;
      @  also
      @    ensures \result <==> 
      @        e1 != null ==>
      @        (new JMLValueSequence(e1)).itemAt(0).equals(e1);
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertFront(e1).first().equals(e1);
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertBack(e1).last().equals(e1);
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertFront(e1).itemAt(0).equals(e1);
      @  also
      @    ensures \result <==>
      @        s.insertFront(e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        e1 != null ==>
      @        s.insertBack(e1).itemAt(s.size()).equals(e1);
      @  also
      @    ensures \result <==>
      @        s.insertBack(e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==> 
      @    // !FIXME! The following may be inconsistent: argument to itemAt might
      @    // be equal to size, but it is required to be less than size.
      @        -1 <= n && n < s.size() && e1 != null
      @          ==> s.insertAfterIndex(n, e1).itemAt(n+1).equals(e1);
      @  also
      @    ensures \result <==> 
      @        -1 <= n && n < s.size()
      @          ==> s.insertAfterIndex(n, e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        0 <= n && n <= s.size() && e1 != null
      @          ==> s.insertBeforeIndex(n, e1).itemAt(n).equals(e1);
      @  also
      @    ensures \result <==> 
      @        0 <= n && n <= s.size()
      @          ==> s.insertBeforeIndex(n, e1).size() == s.size() + 1;
      @  also
      @    ensures \result <==>
      @        s.isPrefix(s2)
      @           == (\forall int i; 0 <= i && i < s.int_length();
      @                  (s2.itemAt(i) != null 
      @                   && s2.itemAt(i).equals(s.itemAt(i)))
      @               || (s2.itemAt(i) == null && s.itemAt(i) == null) );
      @  also
      @    ensures \result <==>
      @        s.isSubsequence(s2)
      @           == s.int_length() <= s2.int_length()
      @              && (s.isPrefix(s2) || s.isSubsequence(s2.trailer()) );
      @ 
      @   // The following are all defined as abbreviations.
      @
      @ also
      @   ensures \result <==>
      @      s.isEmpty() == (s.size() == 0);
      @ also
      @   ensures \result <==>
      @      s.isEmpty() == (s.length == 0);
      @ also
      @   ensures \result <==>
      @      (new JMLValueSequence(e1)).equals(
      @                  new JMLValueSequence().insertFront(e1));
      @ also
      @   ensures \result <==>
      @      (new JMLValueSequence(e1)).equals(
      @                  new JMLValueSequence().insertBack(e1));
      @ also
      @   ensures \result <==>
      @      (new JMLValueSequence(e1)).equals(
      @                  new JMLValueSequence().insertAfterIndex(-1, e1));
      @ also
      @   ensures \result <==>
      @      (new JMLValueSequence(e1)).equals(
      @                  new JMLValueSequence().insertBeforeIndex(0, e1));
      @ also
      @   ensures \result <==>
      @      (s.size() >= 1 ==> s.equals(s.trailer().insertFront(s.first())));
      @ also
      @   ensures \result <==>
      @      (s.size() >= 1 ==> s.equals(s.header().insertBack(s.last())));
      @ also
      @   ensures \result <==>
      @      s.isProperSubsequence(s2)
      @            == ( s.isSubsequence(s2) && !s.equals(s2));
      @ also
      @   ensures \result <==>
      @      s.isSupersequence(s2) == s2.isSubsequence(s);
      @ also
      @   ensures \result <==>
      @      s.isProperSupersequence(s2) == s2.isProperSubsequence(s);
      @ |}
      @
      @ // other ways to specify some operations
      @ implies_that   
      @  ensures \result <==> (new JMLValueSequence()).isEmpty();
      public pure model boolean equational_theory(JMLValueSequence s,
                                                  JMLValueSequence s2,
                                                  JMLType e1,
                                                  JMLType e2, \bigint n);
      @*/

    //@ public invariant elementType <: \type(JMLType);
    /*@ public invariant
      @           (\forall JMLType o; o != null && has(o);
      @                                 \typeof(o) <: elementType);
      @*/

    //@ public invariant_redundantly isEmpty() ==> !containsNull;

    /** The list representing this sequence's elements, in order.
     */
    protected final JMLListValueNode theSeq;
    //@                                 in objectState;
    //@                  maps theSeq.elementState \into elementState;

    //@ invariant theSeq != null ==> theSeq.owner == this;

    /** This sequence's length.
     */
    protected final BigInteger _length;
    //@                    in objectState;
    //@ public model \bigint length;
    //@ protected represents length <- bigIntegerToBigint(_length);

    //@ protected invariant theSeq == null <==> length == 0;
    //@ protected invariant length >= 0;
    
    /*@ protected invariant theSeq != null ==> length == theSeq.length();
      @  protected invariant length == length();
      @*/

    //@ public invariant owner == null;

    //************************* Constructors ********************************

    /** Initialize this to be the empty sequence.
     *  @see #EMPTY
     */
    /*@  public normal_behavior
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures isEmpty();
      @    ensures_redundantly size() == 0;
      @    ensures_redundantly (* this is an empty sequence *);
      @*/
    //@ implies_that
    //@    ensures elementType <: \type(JMLType) && !containsNull;
    public JMLValueSequence() {
        //@ set owner = null;
        theSeq = null;
        _length = BigInteger.ZERO;
        //@ set elementType = \type(JMLType);
        //@ set containsNull = false;
    }  

    /** Initialize this to be the sequence containing just the given element.
     *  @param e the element that is the first element in this sequence.
     *  @see #singleton
     */
    public JMLValueSequence (JMLType e)
        /*@  public normal_behavior
          @    assignable objectState, elementType, containsNull, owner;
          @    ensures int_length() == 1;
          @    ensures (e == null ==> itemAt(0) == null)
          @         && (e != null ==> itemAt(0).equals(e)); 
          @    ensures_redundantly
          @        (* this is a sequence containing just e *); 
      @ also
      @  public model_program {
      @    JMLType copy = (JMLType)e.clone();
      @    behavior
      @      assignable this.*;
      @      ensures objectAt(0) == copy && int_length() == 1;
      @  }
          @*/
    {
        //@ set owner = null;
        theSeq = JMLListValueNode.cons(e, null); // cons() clones e, if needed
        _length = BigInteger.ONE;
        //@ set elementType = (e == null ? \type(JMLType) : \typeof(e));
        //@ set containsNull = (e == null);
	//@ set theSeq.owner = this;
    }

    /** Initialize this sequence based on the given representation.
     */
    //@    requires ls == null <==> len == 0;
    //@    requires len >= 0;
    //@    assignable objectState, elementType, containsNull, owner;
    //@    ensures ls != null ==> elementType == ls.elementType;
    //@    ensures ls != null ==> containsNull == ls.containsNull;
    //@    ensures ls == null ==> elementType <: \type(JMLType);
    //@    ensures ls == null ==> !containsNull;
    /*@
    model protected JMLValueSequence (JMLListValueNode ls, \bigint len) {
        //@ set owner = null;
        theSeq = ls;	
        _length = bigintToBigInteger(len);
        //@ set elementType = ((ls == null) ? \type(JMLType) : ls.elementType);
        //@ set containsNull = ((ls == null) ? false : ls.containsNull);
	//@ set theSeq.owner = this;
    }@*/

    /** Initialize this sequence based on the given representation.
     */
    //@    requires ls == null <==> len == 0;
    //@    requires len >= 0;
    //@    assignable objectState, elementType, containsNull, owner;
    //@    ensures ls != null ==> elementType == ls.elementType;
    //@    ensures ls != null ==> containsNull == ls.containsNull;
    //@    ensures ls == null ==> elementType <: \type(JMLType);
    //@    ensures ls == null ==> !containsNull;
    protected JMLValueSequence (JMLListValueNode ls, int len) {
        //@ set owner = null;
        theSeq = ls;	
        _length = BigInteger.valueOf(len);
        /*@ set elementType = ((ls == null) ? \type(JMLType)
          @                                 : ls.elementType);
          @*/
        //@ set containsNull = ((ls == null) ? false : ls.containsNull);
    }

    //**************************** Static methods ****************************

    /** The empty JMLValueSequence.
     *  @see #JMLValueSequence()
     */
    public static final /*@ non_null @*/ JMLValueSequence EMPTY
        = new JMLValueSequence();

    /** Return the singleton sequence containing the given element.
     *  @see #JMLValueSequence(JMLType)
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures \result != null && \result.equals(new JMLValueSequence(e));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLValueSequence singleton(JMLType e)
    {
        return new JMLValueSequence(e);
    }

    /** Return the sequence containing all the elements in the given
     * array in the same order as the elements appear in the array.
     */
    /*@ public normal_behavior
      @    requires a != null;
      @    assignable \nothing;
      @    ensures \result != null && \result.size() == a.length
      @         && (\forall int i; 0 <= i && i < a.length;
      @                            (\result.itemAt(i) == null 
      @                               ? a[i] == null
      @                               : \result.itemAt(i).equals(a[i])));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLValueSequence convertFrom(/*@ non_null @*/JMLType[] a)
    {
        /*@ non_null @*/ JMLValueSequence ret = EMPTY;
        for (int i = a.length-1; 0 <= i; i--) {
            ret = ret.insertFront(a[i]);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return the sequence containing the first 'size' elements in the given
     * array in the same order as the elements appear in the array.
     */
    /*@ public normal_behavior
      @    requires a != null && 0 <= size && size < a.length;
      @    assignable \nothing;
      @    ensures \result != null && \result.size() == size
      @         && (\forall int i; 0 <= i && i < size;
      @                            (\result.itemAt(i) == null 
      @                               ? a[i] == null
      @                               : \result.itemAt(i).equals(a[i])));
      @
      @ implies_that
      @    requires size < a.length;
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLValueSequence convertFrom(/*@ non_null @*/JMLType[] a, int size)
    {
        /*@ non_null @*/ JMLValueSequence ret = EMPTY;
        for (int i = size-1; 0 <= i; i--) {
            ret = ret.insertFront(a[i]);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return the sequence containing all the value in the
     *  given collection in the same order as the elements appear in the
     *  collection.
     *
     *  @throws ClassCastException if some element in c is not an instance of 
     * JMLType.
     *  @see #containsAll(java.util.Collection)
     */
    /*@   public normal_behavior
      @      requires c != null
      @           && c.elementType <: \type(JMLType);
      @      requires c.size() < Integer.MAX_VALUE;
      @      assignable \nothing;
      @      ensures \result != null && \result.size() == c.size()
      @           && (\forall JMLType x; c.contains(x) <==> \result.has(x))
      @           && (* the elements in \result are in the same order as c *);
      @  also
      @    public exceptional_behavior
      @      requires c != null && (\exists Object o; c.contains(o);
      @                                  !(o instanceof JMLType));
      @      assignable \nothing;
      @      signals_only ClassCastException;
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLValueSequence convertFrom(/*@ non_null @*/ java.util.Collection c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLValueSequence ret = EMPTY;
        java.util.Iterator celems = c.iterator();
        while (celems.hasNext()) {
            Object o = celems.next();
            if (o == null) {
                ret = ret.insertBack(null);
            } else {
                //@ assume o instanceof JMLType;
                ret = ret.insertBack((JMLType) o);
            }
        }
        return ret;
    } //@ nowarn Exception;

    /** Return the sequence containing all the value in the
     *  given JMLCollection in the same order as the elements appear in the
     *  collection.
     *
     *  @throws ClassCastException if some element in c is not an instance of 
     * JMLType.
     */
    /*@   public normal_behavior
      @      requires c != null
      @           && c.elementType <: \type(JMLType);
      @      requires c.size() < Integer.MAX_VALUE;
      @      assignable \nothing;
      @      ensures \result != null
      @           && (\forall JMLType x; c.has(x) <==> \result.has(x))
      @           && (* the elements in \result are in the same order as c *);
      @      ensures_redundantly \result.size() == c.size();
      @  also
      @    public exceptional_behavior
      @      requires c != null && (\exists Object o; c.has(o);
      @                                  !(o instanceof JMLType));
      @      assignable \nothing;
      @      signals_only ClassCastException;
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLValueSequence convertFrom(/*@ non_null @*/ JMLCollection c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLValueSequence ret = EMPTY;
        JMLIterator celems = c.iterator();
        while (celems.hasNext()) {
            Object o = celems.next();
            if (o == null) {
                ret = ret.insertBack(null);
            } else {
                //@ assume o instanceof JMLType;
                ret = ret.insertBack((JMLType) o);
            }
        }
        return ret;
    } //@ nowarn Exception;

    //**************************** Observers **********************************

    /** Return the element at the given zero-based index.
     *  @param i the zero-based index into the sequence.
     *  @exception JMLSequenceException if the index oBiI is out of range.
     *  @see #get(int)
     *  @see #has(JMLType)
     *  @see #count(JMLType)
     */
    /*@ // _ alsoIfValue _ //FIXME! later
      @  public normal_behavior
      @    requires 0 <= i && i < length;
      @    ensures 
      @       (* \result == null, if the ith element of this is null;
      @          otherwise, \result ".equals" the ith element of this *);
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length);
      @    signals_only JMLSequenceException;
      @ for_example
      @   public normal_example
      @     requires (* this is <w,x,y,z> and i is 0 *);
      @     ensures (* \result is w.clone() *);
      @  also
      @   public normal_example
      @     requires (* this is <w,x,y,z> and i is 3 *);
      @     ensures (* \result is z.clone() *);
      @*/ 
    /*@
    model public JMLType itemAt(\bigint i) throws JMLSequenceException {
        if (i < 0 || i >= this.length) {
            throw new JMLSequenceException("Index out of range.");
        } else {
            JMLListValueNode thisWalker = theSeq;
	  
            \bigint k = 0;
            loop_invariant 0 <= k && k <= i && thisWalker != null;
            for (; k < i; k=k+1) {
                assume thisWalker.next != null;
                thisWalker = thisWalker.next;
            }   
            return (thisWalker.head());  // head() clones if necessary
        }
    }    
    @*/

    /** Return the element at the given zero-based index.
     *  @param i the zero-based index into the sequence.
     *  @exception JMLSequenceException if the index i is out of range.
     *  @see #get(int)
     *  @see #has(JMLType)
     *  @see #count(JMLType)
     *  @see #itemAt(\bigint)
     */
    /*@ also
      @  public normal_behavior
      @    requires 0 <= i && i < int_size();
      @    ensures 
      @       (* \result == null, if the ith element of this is null;
      @          otherwise, \result ".equals" the ith element of this *);
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < int_size());
      @    signals_only JMLSequenceException;
      @ for_example
      @   public normal_example
      @     requires (* this is <w,x,y,z> and i is 0 *);
      @     ensures (* \result is w.clone() *);
      @  also
      @   public normal_example
      @     requires (* this is <w,x,y,z> and i is 3 *);
      @     ensures (* \result is z.clone() *);
      @*/
    public JMLType itemAt(int i) throws JMLSequenceException {
        if (i < 0 || i >= int_length()) {
            throw new JMLSequenceException("Index out of range.");
        } else {
            JMLListValueNode thisWalker = theSeq;
	      
            int k = 0;
            //@ loop_invariant 0 <= k && k <= i && thisWalker != null;
            for (; k < i; k++) {
                //@ assume thisWalker.next != null;
                thisWalker = thisWalker.next;
            }   
            return (thisWalker.head());  // head() clones if necessary
        }
    }    

    /** Return the element at the given zero-based index; a synonym
     *  for {@link #itemAt}.
     *  @param i the zero-based index into the sequence.
     *  @exception IndexOutOfBoundsException if the index i is out of range.
     *  @see #itemAt(\bigint)
     */
    /*@  public normal_behavior
      @    requires 0 <= i && i < length; //FIXME, might use size();
      @    ensures 
      @       (* \result == null, if the ith element of this is null;
      @          otherwise, \result ".equals" the ith element of this *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length); //FIXME, might use size());
      @    signals_only IndexOutOfBoundsException;
      @
      @ implies_that
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @*/
    /*@ model public JMLType get(\bigint i) throws IndexOutOfBoundsException {
      try {
        JMLType ret = itemAt(i);
        //@ assume ret != null ==> \typeof(ret) <: elementType;
        //@ assume !containsNull ==> ret != null;
        return ret;
      } catch (JMLSequenceException e) {
         IndexOutOfBoundsException e2 = new IndexOutOfBoundsException();
         e2.initCause(e);
         throw e2;
      }
    }
    @*/

    /** Return the element at the given zero-based index; a synonym
     *  for {@link #itemAt}.
     *  @param i the zero-based index into the sequence.
     *  @exception IndexOutOfBoundsException if the index i is out of range.
     *  @see #itemAt(int)
     */
    /*@  public normal_behavior
      @    requires 0 <= i && i < length;
      @    ensures 
      @       (* \result == null, if the ith element of this is null;
      @          otherwise, \result ".equals" the ith element of this *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= i && i < length);
      @    signals_only IndexOutOfBoundsException;
      @
      @ implies_that
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @*/
    public JMLType get(int i) throws IndexOutOfBoundsException {
        try {
            JMLType ret = itemAt(i);
            //@ assume ret != null ==> \typeof(ret) <: elementType;
            //@ assume !containsNull ==> ret != null;
            return ret;
        } catch (JMLSequenceException e) {
            IndexOutOfBoundsException e2 = new IndexOutOfBoundsException();
            e2.initCause(e);
            throw e2;
        }
    }  

    /** Tells the number of elements in the sequence; a synonym for
     * {@link #length}.
     * @see #length()
     * @see #isEmpty()
     */
    /*@
      @ public model pure \bigint size() {
      @   return length;
      @ } 
      @*/

    /** Tells the number of elements in the sequence; a synonym for
     * {@link #length}.
     * @see #size()
     * @see #isEmpty()
     */
    /*@
      @ public model pure \bigint length() {
      @   return length;
      @ } 
      @*/

    /** Tells the number of elements in the sequence; a synonym for
     * {@link #length}.
     * @see #length()
     * @see #isEmpty()
     */
    /*@ also
      @ protected normal_behavior
      @    requires size() <= Integer.MAX_VALUE;
      @    ensures \result == size();
      @
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d> *);
      @     ensures \result == 4;
      @  also
      @   public normal_example
      @     requires (* this is <> *);
      @     ensures \result == 0;
      @*/
    public int int_size( ) {
        return _length.intValue();
    }  

    /** Tells the number of elements in the sequence; a synonym for
     * {@link #size}.
     * @see #int_size()
     */
    /*@ also
      @    public normal_behavior
      @      requires size() <= Integer.MAX_VALUE;
      @      ensures \result == size();
      @*/
    public int int_length( ) {
        return _length.intValue();
    }  

    /** Tells the number of times a given element occurs in the sequence.
     *  @see #has(JMLType)
     *  @see #itemAt(int)
     */
    /*@ //also //FIXME, remove // later
      @   public normal_behavior
      @     requires item != null;
      @     ensures \result
      @          == (\num_of \bigint i; 0 <= i && i < length();
      @                             itemAt(i) != null
      @                             && itemAt(i).equals(item));
      @ also
      @   public normal_behavior
      @     requires item == null;
      @     ensures \result == (\num_of \bigint i; 0 <= i && i < length();
      @                                        itemAt(i) == null);
      @*/
    /*@
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,c> and item is c *);
      @     ensures \result == 2;
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,a> and item is q *);
      @     ensures \result == 0;
      @*/
    /*@
    model public \bigint bi_count(JMLType item) {
        JMLListValueNode ptr = this.theSeq;
        \bigint cnt = 0;
         maintaining (* cnt is count of elements matching item so far *);
        while (ptr != null) {
            if (ptr.headEquals(item)) {
                cnt = cnt + 1;
            }
            ptr = ptr.next;
        }
        return cnt;
    }
    @*/

    /** Tells the number of times a given element occurs in the sequence.
     *  @see #has(JMLType)
     *  @see #itemAt(int)
     */
    /*@ also
      @   public normal_behavior
      @     requires item != null;
      @     ensures \result
      @          == (\num_of int i; 0 <= i && i < int_length();
      @                             itemAt(i) != null
      @                             && itemAt(i).equals(item));
      @ also
      @   public normal_behavior
      @     requires item == null;
      @     ensures \result == (\num_of int i; 0 <= i && i < int_length();
      @                                        itemAt(i) == null);
      @*/
    /*@
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,c> and item is c *);
      @     ensures \result == 2;
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,a> and item is q *);
      @     ensures \result == 0;
      @*/
    public int count(JMLType item) {
        JMLListValueNode ptr = this.theSeq;
        int cnt = 0;
        //@ maintaining (* cnt is count of elements matching item so far *);
        while (ptr != null) {
            if (ptr.headEquals(item)) {
                cnt++;
            }
            ptr = ptr.next;
        }
        return cnt;
    }

    /** Tells whether the given element is ".equals" to an
     * element in the sequence.
     * @see #count(JMLType)
     */
    /*@ also
      @   public normal_behavior
      @    {|
      @       requires elem != null;
      @       ensures \result <==> 
      @                 (\exists int i; 0 <= i && i < int_length();
      @                                 itemAt(i).equals(elem));
      @      also
      @       requires elem == null;
      @        ensures \result <==> 
      @                  (\exists int i; 0 <= i && i < int_length(); 
      @                                  itemAt(i) == null);
      @    |}
      @ for_example
      @   public normal_example
      @     requires (* this is <w,x,y,z> and elem is x *);
      @     ensures (* \result is true *);
      @  also
      @   public normal_example
      @     requires isEmpty();
      @     ensures !\result;
      @*/
    public boolean has(JMLType elem) {
        return theSeq != null && theSeq.has(elem);
    }  

    /** Tell whether, for each element in the given collection, there is a
     * ".equals" element in this sequence.
     *  @param c the collection whose elements are sought.
     */
    /*@ public normal_behavior
      @    requires c != null;
      @    ensures \result <==> (\forall Object o; c.contains(o); this.has(o));
      @*/
    public boolean containsAll(/*@ non_null @*/ java.util.Collection c) {
        java.util.Iterator celems = c.iterator();
        while (celems.hasNext()) {
            Object o = celems.next();
            if (!has(o)) {
                return false;
            }
        }
        return true;
    }  

    /** Tells whether the elements of the this sequence occur, in
     * order, at the beginning of the given sequence, using
     * ".equals" for comparisons.
     *  @see #isProperPrefix
     *  @see #isSuffix
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @      int_length() <= s2.int_length()
      @      && (\forall int i; 0 <= i && i < int_length();
      @                   (s2.itemAt(i) != null 
      @                    && s2.itemAt(i).equals(itemAt(i)))
      @                || (s2.itemAt(i) == null && itemAt(i) == null) );
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c> and s2 is <a,b,c,d> *);
      @     ensures (* \result is true *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c> and s2 is <a,b,c> *);
      @     ensures (* \result is true *);
      @  also
      @   public normal_example
      @     requires (* this is <> and s2 is <a,b,c,d> *);
      @     ensures (* \result is true *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d> and s2 is <a,b,c> *);
      @     ensures (* \result is false *);
      @*/
    public boolean isPrefix(/*@ non_null @*/ JMLValueSequence s2) {
        return int_length() <= s2.int_length()
            && (theSeq == null || theSeq.isPrefixOf(s2.theSeq));
    }  

    /** Tells whether this sequence is shorter than the given
     *  sequence, and also if the elements of this sequence occur, in
     *  order, at the beginning of the given sequence, using
     *  ".equals" for comparisons.
     *  @see #isPrefix
     *  @see #isProperSuffix
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> this.isPrefix(s2) && !this.equals(s2);
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c> and s2 is <a,b,c,d> *);
      @     ensures (* \result is true *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c> and s2 is <a,b,c> *);
      @     ensures (* \result is false *);
      @*/
    public boolean isProperPrefix(/*@ non_null @*/ JMLValueSequence s2) {
        return int_length() != s2.int_length() && isPrefix(s2);
    }  

    /** Tells whether the elements of this sequence occur, in order,
     *  at the end of the given sequence, using ".equals" for
     *  comparisons.
     *  @see #isProperSuffix
     *  @see #isPrefix
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @       int_length() <= s2.int_length()
      @       && this.equals(s2.removePrefix(s2.int_length() - int_length()));
      @ for_example
      @   public normal_example
      @     requires (* this is <b,c,d> and s2 is <a,b,c,d> *);
      @     ensures (* \result is true *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c> and s2 is <a,b,c,d> *);
      @     ensures (* \result is false *);
      @  also
      @   public normal_example
      @     requires (* this is <> and s2 is <a,b,c,d> *);
      @     ensures (* \result is true *);
      @*/
    public boolean isSuffix(/*@ non_null @*/ JMLValueSequence s2) {
        if (int_length() > s2.int_length()) {
            return false;
        } else if (int_length() == 0) {
            return true;
        } 
        //@ assert int_length() != 0 && int_length() <= s2.int_length();
        //@ hence_by (* arithmetic and int_length() >= 0 and the invariant *);
        //@ assert theSeq != null && s2.int_length() > 0;
        JMLListValueNode suffix = s2.theSeq.removePrefix(s2.int_length() - int_length());
        return theSeq.equals(suffix);
    }  

    /** Tells whether the this sequence is shorter than the given
     *  object, and also if the elements of this sequence occur, in
     *  order, at the end of the given sequence, using
     *  ".equals" for comparisons.
     *  @see #isSuffix
     *  @see #isProperPrefix
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> this.isSuffix(s2) && !this.equals(s2);
      @*/
    public boolean isProperSuffix(/*@ non_null @*/ JMLValueSequence s2) {
        return int_length() != s2.int_length() && isSuffix(s2);
    }  

    /** Test whether this object's value is equal to the given argument.
     *  @see #isSuffix
     *  @see #int_size()
     */
    /*@ also
      @  public normal_behavior
      @    requires obj != null && obj instanceof JMLValueSequence;
      @     ensures \result <==>
      @          isPrefix((JMLValueSequence)obj)
      @          && ((JMLValueSequence)obj).isPrefix(this);
      @     ensures_redundantly \result ==>
      @          containsNull == ((JMLValueSequence)obj).containsNull;
      @ also
      @  public normal_behavior
      @    requires obj == null || !(obj instanceof JMLValueSequence);
      @    ensures !\result;
      @*/
    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object obj) {
        return (obj != null && obj instanceof JMLValueSequence)
            && (int_length() == ((JMLValueSequence)obj).int_length())
            && isPrefix((JMLValueSequence)obj);
    }  

    /** Return a hash code for this object.
     */
    public int hashCode() {
        return (theSeq == null ? 0 : theSeq.hashCode());
    }

    /** Tells whether this sequence is empty.
     *  @see #int_size()
     *  @see #int_length()
     */
    /*@  public normal_behavior
      @    ensures \result == (int_length() == 0);
      @*/
    public /*@ pure @*/ boolean isEmpty() {
        return theSeq == null;
    }

    /** Return the zero-based index of the first occurrence of the given
     *  element in the sequence, if there is one
     * @param item the JMLType sought in this.
     * @return the first index at which item occurs.
     * @exception JMLSequenceException if item is not a member of the sequence.
     * @see #itemAt(int)
     */
    /*@  public normal_behavior
      @    requires has(item);
      @    {|
      @       requires item != null;
      @       ensures itemAt(\result).equals(item)
      @             && (\forall \bigint i; 0 <= i && i < \result;
      @                                !(itemAt(i).equals(item)));
      @       ensures_redundantly (* \result is the first index
      @                                at which item occurs in this *);
      @     also
      @      requires item == null;
      @      ensures itemAt(\result) == null
      @           && (\forall \bigint i; 0 <= i && i < \result;
      @                              itemAt(i) != null);
      @    |}
      @ also
      @  public exceptional_behavior
      @    requires !has(item);
      @    signals_only JMLSequenceException;
      @ for_example
      @   public normal_example
      @     requires (* this is <w,x,y,z,x> and item is x *);
      @     ensures (* \result is 1 *);
      @*/
    /*@
    model public \bigint bi_indexOf(JMLType item) throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException(ITEM_PREFIX + item + IS_NOT_FOUND);
        }
        \bigint idx = theSeq.bi_indexOf(item); 
        if (idx == -1) {
            throw new JMLSequenceException(ITEM_PREFIX + item + IS_NOT_FOUND);
        } else {
            return idx;
        }
    }
    @*/

    /** Return the zero-based index of the first occurrence of the given
     *  element in the sequence, if there is one
     * @param item the JMLType sought in this.
     * @return the first index at which item occurs.
     * @exception JMLSequenceException if item is not a member of the sequence.
     * @see #itemAt(int)
     */
    /*@  public normal_behavior
      @    requires has(item);
      @    {|
      @       requires item != null;
      @       ensures itemAt(\result).equals(item)
      @             && (\forall int i; 0 <= i && i < \result;
      @                                !(itemAt(i).equals(item)));
      @       ensures_redundantly (* \result is the first index
      @                                at which item occurs in this *);
      @     also
      @      requires item == null;
      @      ensures itemAt(\result) == null
      @           && (\forall int i; 0 <= i && i < \result;
      @                              itemAt(i) != null);
      @    |}
      @ also
      @  public exceptional_behavior
      @    requires !has(item);
      @    signals_only JMLSequenceException;
      @ for_example
      @   public normal_example
      @     requires (* this is <w,x,y,z,x> and item is x *);
      @     ensures (* \result is 1 *);
      @*/
    public int indexOf(JMLType item) throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException(ITEM_PREFIX + item + IS_NOT_FOUND);
        }
        int idx = theSeq.indexOf(item);
        if (idx == -1) {
            throw new JMLSequenceException(ITEM_PREFIX + item + IS_NOT_FOUND);
        } else {
            return idx;
        }
    }

    private static final String ITEM_PREFIX = "item ";
    private static final String IS_NOT_FOUND = " is not in this sequence.";

    /** Return the first element in this sequence.
     *  @exception JMLSequenceException if the sequence is empty.
     * @see #itemAt(int)
     * @see #last
     * @see #trailer
     * @see #header
     */
    /*@ also
      @  public normal_behavior
      @    requires int_length() > 0;
      @    {|
      @       requires itemAt(0) != null;
      @       ensures \result.equals(itemAt(0));
      @      also
      @       requires itemAt(0) == null;
      @       ensures \result == null;
      @    |}
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals_only JMLSequenceException;
      @ implies_that
      @   public normal_behavior
      @     requires int_length() > 0;
      @     ensures \result != null ==> \typeof(\result) <: elementType;
      @     ensures !containsNull ==> \result != null;
      @ for_example
      @   public normal_example
      @     requires (* this is <b,c,d> *);
      @     ensures (* \result is b.clone() *);
      @*/
    public /*@ pure @*/ JMLType first() throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried first() on empty sequence.");
        } else {
            return (theSeq.head());  // head() clones if necessary
        }   
    }

    /** Return the last element in this sequence.
     *  @exception JMLSequenceException if the sequence is empty.
     * @see #itemAt(int)
     * @see #first
     * @see #header
     * @see #trailer
     */
    /*@ also
      @  public normal_behavior
      @    requires int_length() >= 1;
      @    {|
      @       requires itemAt((int)(int_length()-1)) != null;
      @       ensures \result.equals(itemAt((int)(int_length()-1)));
      @     also
      @       requires itemAt((int)(int_length()-1)) == null;
      @       ensures \result == null;
      @    |}
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals_only JMLSequenceException;
      @ implies_that
      @   public normal_behavior
      @     requires int_length() >= 1;
      @     ensures \result != null ==> \typeof(\result) <: elementType;
      @     ensures !containsNull ==> \result != null;
      @ for_example
      @   public normal_example
      @     requires (* this is <b,c,d> *);
      @     ensures (* \result is d.clone() *);
      @*/
    public JMLType last() throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried last() on empty sequence.");
        } else {
            return theSeq.last();  // last() clones if necessary
        }   
    }

    /** Tells whether this sequence is a subsequence of the given sequence.
     *  @param s2 the sequence to search for within this sequence.
     *  @return whether the elements of this occur (in order) within s2.
     * @see #isProperSubsequence
     * @see #isSupersequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @                 int_length() <= s2.int_length()
      @              && (\exists int i; 0 <= i && i < s2.int_length()-int_length()+1;
      @                                 isPrefix(s2.removePrefix(i)));
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c> and s2 is <a,b,c,d> *);
      @     ensures (* \result is true *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c> and s2 is <a,b,c> *);
      @     ensures (* \result is true *);
      @  also
      @   public normal_example
      @     requires (* this is <> and s2 is <a,b,c,d> *);
      @     ensures (* \result is true *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d> and s2 is <a,b,c> *);
      @     ensures (* \result is false *);
      @*/
    public boolean isSubsequence(/*@ non_null @*/ JMLValueSequence s2) {
        JMLListValueNode walker = s2.theSeq;
        for (int walkerLen = s2.int_length(); int_length() <= walkerLen; walkerLen--) {
            if (theSeq == null || theSeq.isPrefixOf(walker)) {
                return true;
            }
            walker = walker.next;
        }   
        return false;
    }  

    /** Tells whether this sequence is strictly shorter than the given
     *  sequence and a subsequence of it.
     *  @param s2 the sequence to search for within this sequence.
     *  @return whether the elements of s2 occur (in order) within this.
     * @see #isSubsequence
     * @see #isProperSupersequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @        this.isSubsequence(s2) && !this.equals(s2);
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c> and s2 is <a,b,c,d> *);
      @     ensures (* \result is true *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c> and s2 is <a,b,c> *);
      @     ensures (* \result is false *);
      @  also
      @   public normal_example
      @     requires (* this is <> and s2 is <a,b,c,d> *);
      @     ensures (* \result is false *);
      @*/
    public boolean isProperSubsequence(/*@ non_null @*/ JMLValueSequence s2) {
        return int_length() < s2.int_length() && isSubsequence(s2);
    }  

    /** Tells whether the given sequence is a supersequence of this sequence.
     *  @param s2 the sequence to search within for this sequence.
     *  @return whether the elements of this occur (in order) within s2.
     * @see #isProperSubsequence
     * @see #isSubsequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> s2.isSubsequence(this);
      @*/
    public boolean isSupersequence(/*@ non_null @*/ JMLValueSequence s2) {
        return s2.isSubsequence(this);
    }

    /** Tells whether the given sequence is both longer than and a
     *  supersequence of this sequence.
     *  @param s2 the sequence to search within for this sequence.
     *  @return whether the elements of this occur (in order) within s2.
     * @see #isSupersequence
     * @see #isProperSubsequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==> s2.isProperSubsequence(this);
      @*/
    public
        boolean isProperSupersequence(/*@ non_null @*/ JMLValueSequence s2) {
        return s2.isProperSubsequence(this);
    }  

    /** Tells whether this sequence is the result of inserting the
     *  given element once into the given sequence.  That is, this
     *  sequence is exactly one element longer than the given
     *  sequence, and its elements are in the same order, except for
     *  the insertion of the given element.
     *  @param s2 the shorter sequence, which we see if the elem is
     *            inserted into
     *  @param elem the given element
     *  @return whether the elements of s2 occur in order in this
     *          sequence, with the insertion of elem somewhere.
     * @see #isDeletionFrom
     * @see #isProperSupersequence
     * @see #isProperSubsequence
     * @see #subsequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @         (\exists int i; 0 <= i && i < int_length();
      @                         itemAt(i).equals(elem)
      @                         && subsequence(0,i)
      @                            .concat(subsequence((int)(i+1),int_length()))
      @                            .equals(s2));
      @    ensures_redundantly \result ==> this.int_length() == s2.int_length()+1;
      @    ensures_redundantly \result ==> has(elem);
      @    ensures_redundantly \result <==> s2.isDeletionFrom(this, elem);
      @*/
    public boolean isInsertionInto(/*@ non_null @*/ JMLValueSequence s2,
                                   JMLType elem) {
        if (int_length() != s2.int_length() + 1) {
            return false;
        }
        JMLListValueNode walker = theSeq;
        JMLListValueNode s2walker = s2.theSeq;
        /*@ maintaining subsequence(0, (int)(int_length()-lenRemaining))
          @                 .equals(s2.subsequence(0, (int)(int_length()-lenRemaining)));
          @ decreasing int_length();
          @*/
        for (int lenRemaining = int_length(); lenRemaining > 0; lenRemaining--) {
            if (walker.headEquals(elem)) {
                if ((walker.next == null && s2walker == null)
                    || (walker.next != null && walker.next.equals(s2walker))) {
                    return true;
                }
            }
            if (s2walker == null || !s2walker.headEquals(walker.head())) {
                return false;
            }
            walker = walker.next;
            s2walker = s2walker.next;
        }   
        return false;
    }  

    /** Tells whether this sequence is the result of deleting the
     *  given element once from the given sequence.  That is, this
     *  sequence is exactly one element shorter than the given
     *  sequence, and its elements are in the same order, except for
     *  the deletion of the given element from the given sequence.
     *  @param s2 the longer sequence, in which we see if the elem is
     *            deleted from
     *  @param elem the given element
     *  @return whether the elements of s2 occur in order in this
     *          sequence, with the deletion of elem somewhere.
     * @see #isInsertionInto
     * @see #isProperSupersequence
     * @see #isProperSubsequence
     * @see #subsequence
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @         (\exists int i; 0 <= i && i < s2.int_length();
      @                         s2.itemAt(i).equals(elem)
      @                         && this.equals(s2.removeItemAt(i)));
      @    ensures_redundantly \result ==> this.int_length()+1 == s2.int_length();
      @    ensures_redundantly \result ==> s2.has(elem);
      @    ensures_redundantly \result <==> s2.isInsertionInto(this, elem);
      @*/
    public boolean isDeletionFrom(/*@ non_null @*/ JMLValueSequence s2,
                                  JMLType elem) {
        return s2.isInsertionInto(this, elem);
    }  

    // *************** building new JMLValueSequences **********************

    /** Return a clone of this object.  This method clones the
     * elements of the sequence.
     */
    /*@ also
      @  public normal_behavior
      @   ensures \result != null
      @        && \result instanceof JMLValueSequence
      @        && ((JMLValueSequence)\result).equals(this);
      @*/
    public /*@ non_null @*/ Object clone() { 
        if (theSeq == null) {
            return this;
        } else {
            return new JMLValueSequence((JMLListValueNode)theSeq.clone(),
                                        int_length());
        }
    }  

    /** Return a sequence containing the first n elements in this sequence.
     *  @param n the number of elements in the result.
     *  @exception JMLSequenceException if n is negative or greater than
     *  the length of the sequence.
     * @see #trailer
     * @see #removePrefix
     * @see #subsequence
     */
    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == n
      @            && (\forall \bigint i; 0 <= i && i < n;
      @                   (\result.itemAt(i) != null 
      @                    ==> \result.itemAt(i).equals(itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    ==> itemAt(i) == null) );
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with the last length-n items removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals_only JMLSequenceException;
      @
      @ implies_that
      @    ensures !containsNull ==> !\result.containsNull;
      @
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and n is 0 *);
      @     ensures (* \result is <> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and n is 3 *);
      @     ensures (* \result is <a,b,c> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and n is 5 *);
      @     ensures (* \result is <a,b,c,d,e> *);
      @  also
      @   public normal_example
      @     requires n == length;
      @     ensures \result.equals(this);
      @*/
    /*@ model public JMLValueSequence prefix(\bigint n) //FIXME, non_null
        throws JMLSequenceException {
        if (n < 0 || n > length) {
            throw new
                JMLSequenceException("Invalid parameter to prefix() with n = " 
                                     + n + "\n"
                                     + "   when sequence length = " + length);
        } else {
            if (n == 0) {
                return new JMLValueSequence();
            } else {
                JMLListValueNode pfx_list = theSeq.prefix(n);
                assume pfx_list != null;
                assume !containsNull ==> !pfx_list.containsNull;
                return new JMLValueSequence(pfx_list, n);
            }
        }
    }  
    @*/

	/** Return a sequence containing the first n elements in this sequence.
	 *  @param n the number of elements in the result.
	 *  @exception JMLSequenceException if n is negative or greater than
	 *  the length of the sequence.
	 * @see #trailer
	 * @see #removePrefix
	 * @see #subsequence
	 */
    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == n
      @            && (\forall int i; 0 <= i && i < n;
      @                   (\result.itemAt(i) != null 
      @                    ==> \result.itemAt(i).equals(itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    ==> itemAt(i) == null) );
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with the last length-n items removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals_only JMLSequenceException;
      @
      @ implies_that
      @    ensures !containsNull ==> !\result.containsNull;
      @
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and n is 0 *);
      @     ensures (* \result is <> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and n is 3 *);
      @     ensures (* \result is <a,b,c> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and n is 5 *);
      @     ensures (* \result is <a,b,c,d,e> *);
      @  also
      @   public normal_example
      @     requires n == this.length;
      @     ensures \result.equals(this);
      @*/
      public /*@ non_null @*/ JMLValueSequence prefix(int n)
	  throws JMLSequenceException {
	  if (n < 0 || n > int_length()) {
	      throw new
		  JMLSequenceException("Invalid parameter to prefix() with n = " 
				       + n + "\n"
				       + "   when sequence length = " + int_length());
	  } else {
	      if (n == 0) {
		  return new JMLValueSequence();
	      } else {
		  JMLListValueNode pfx_list = theSeq.prefix(n);
		  //@ assume pfx_list != null;
		  //@ assume !containsNull ==> !pfx_list.containsNull;
		  return new JMLValueSequence(pfx_list, n);
	      }
	  }
      }  

    /** Return a sequence containing all but the first n elements in this.
     *  @param n the number of elements to remove
     *  @exception JMLSequenceException if n is negative or greater than
     *  the length of the sequence.
     * @see #header
     * @see #prefix
     * @see #subsequence
     */
    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == length - n
      @        && (\forall \bigint i; n <= i && i < length;
      @                  (\result.itemAt(i-n) != null 
      @                   && \result.itemAt(i-n).equals(itemAt(i)))
      @               || (\result.itemAt(i-n) == null 
      @                   && itemAt(i) == null) );
      @    ensures_redundantly 
      @          (* \result is the same as this,
      @             but with the first n items removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals_only JMLSequenceException;
      @*/
    //@ implies_that
    //@    ensures !containsNull ==> !\result.containsNull;
    /*@
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and n is 1 *);
      @     ensures (* \result is <b,c,d,e> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and n is 5 *);
      @     ensures (* \result is <> *);
      @  also
      @   public normal_example
      @     requires n == this.length;
      @     ensures \result.isEmpty();
      @*/
    /*@
      model public JMLValueSequence removePrefix(\bigint n) //FIXME,  @non_null@
        throws JMLSequenceException {
        if (n < 0 || n > length) {
            throw new
                JMLSequenceException("Invalid parameter to removePrefix() "
                                     + "with n = " + n + "\n"
                                     + "   when sequence length = " + length);
        } else {
            if (n == 0) {
                return this;
            } else {
                JMLListValueNode pfx_list = theSeq.removePrefix(n);
                //@ assume pfx_list == null <==> n == length;
                //@ assume pfx_list != null && !containsNull ==> !pfx_list.containsNull;
                return new JMLValueSequence(pfx_list, length-n);
            }
        }
    }@*/  

    /** Return a sequence containing all but the first n elements in this.
     *  @param n the number of elements to remove
     *  @exception JMLSequenceException if n is negative or greater than
     *  the length of the sequence.
     * @see #header
     * @see #prefix
     * @see #subsequence
     */
    /*@  public normal_behavior
      @    requires 0 <= n && n <= length;
      @    ensures \result.length == length - n
      @        && (\forall \bigint i; n <= i && i < length;
      @                  (\result.itemAt((int)(i-n)) != null 
      @                   && \result.itemAt((int)(i-n)).equals(itemAt(i)))
      @               || (\result.itemAt((int)(i-n)) == null 
      @                   && itemAt(i) == null) );
      @    ensures_redundantly 
      @          (* \result is the same as this,
      @             but with the first n items removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= n && n <= length);
      @    signals_only JMLSequenceException;
      @*/
    //@ implies_that
    //@    ensures !containsNull ==> !\result.containsNull;
    /*@
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and n is 1 *);
      @     ensures (* \result is <b,c,d,e> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and n is 5 *);
      @     ensures (* \result is <> *);
      @  also
      @   public normal_example
      @     requires n == this.length;
      @     ensures \result.isEmpty();
      @*/
    public /*@ non_null @*/ JMLValueSequence removePrefix(int n)
        throws JMLSequenceException {
        if (n < 0 || n > int_length()) {
            throw new
                JMLSequenceException("Invalid parameter to removePrefix() "
                                     + "with n = " + n + "\n"
                                     + "   when sequence length = " + int_length());
        } else {
            if (n == 0) {
                return this;
            } else {
                JMLListValueNode pfx_list = theSeq.removePrefix(n);
                /*@ assume pfx_list == null <==> n == length;
                  @ assume pfx_list != null && !containsNull
                  @        ==> !pfx_list.containsNull;
                  @*/
                return new JMLValueSequence(pfx_list, int_length()-n);
            }
        }
    }  

    /** Return a sequence that is the concatenation of this with
     *  the given sequence.
     *  @param s2 the sequence to place at the end of this sequence in
     *  the result.
     *  @return the concatenation of this sequence and s2.
     */
    /*@  public normal_behavior
      @    requires s2 != null;
      @    ensures \result.int_length() == int_length() + s2.int_length()
      @         && (\forall int i; 0 <= i && i < int_length();
      @                   (\result.itemAt(i) != null 
      @                    && \result.itemAt(i).equals(itemAt(i)))
      @                || (\result.itemAt(i) == null 
      @                    && itemAt(i) == null) )
      @         && (\forall int i; 0 <= i && i < s2.int_length();
      @                   (\result.itemAt((int)(int_length()+i)) != null 
      @                    && \result.itemAt((int)(int_length()+i)).equals(s2.itemAt(i)))
      @                || (\result.itemAt((int)(int_length()+i)) == null 
      @                    && s2.itemAt(i) == null) );
      @    ensures_redundantly 
      @           (* \result is the concatenation of this followed by s2 *);
      @*/
    //@ implies_that
    //@    ensures containsNull || s2.containsNull <==> \result.containsNull;
    /*@
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b> and s2 is <c,d,e> *);
      @     ensures (* \result is <a,b,c,d,e> *);
      @*/
    public /*@ non_null @*/
        JMLValueSequence concat(/*@ non_null @*/ JMLValueSequence s2) {
        if (theSeq == null) {
            return s2;
        } else if (s2.theSeq == null) {
            return this;
        } else {
            JMLListValueNode new_list = theSeq.concat(s2.theSeq);
            /*@ assume new_list != null && int_length() + s2.int_length() > 0;
              @*/
            return new JMLValueSequence(new_list,
                                         int_length() + s2.int_length());
        }
    }  //@ nowarn Post;

    /** Return a sequence that is the reverse of this sequence.
     *  @return the reverse of this sequence.
     */
    /*@  public normal_behavior
      @    old int len = int_length();
      @    ensures \result.int_length() == len
      @         && (\forall int i; 0 <= i && i < len;
      @                   (\result.itemAt((int)(len-i-1)) != null 
      @                    && \result.itemAt((int)(len-i-1)).equals(itemAt(i)))
      @                || (\result.itemAt((int)(len-i-1)) == null 
      @                    && itemAt(i) == null) );
      @    ensures_redundantly 
      @           (* \result has the same elements but with the items 
      @             arranged in the reverse order *);
      @
      @ implies_that
      @    ensures elementType == \result.elementType;
      @    ensures containsNull <==> \result.containsNull;
      @*/
    public /*@ non_null @*/ JMLValueSequence reverse() {
        if (theSeq == null) {
            return this;
        } else {
            JMLListValueNode r = theSeq.reverse();
            return new JMLValueSequence(r, int_length());
        }
    } //@ nowarn Post;

    /** Return a sequence like this, but without the element at the
     *  given zero-based index.
     *  @param index the zero-based index into the sequence.
     *  @exception JMLSequenceException if the index is out of range.
     * @see #itemAt(int)
     * @see #removeItemAt
     * @see #prefix
     * @see #removePrefix
     * @see #subsequence
     * @see #concat
     */
    /*@  public normal_behavior
      @    requires 0 <= index && index < length();
      @    ensures \result.equals(prefix(index).concat(removePrefix(index+1)));
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with the item at position index removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < length());
      @    signals_only JMLSequenceException;
      @
      @ implies_that
      @    ensures !\result.containsNull <== !containsNull;
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and index is 1 *);
      @     ensures (* \result is <a,c,d,e> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and index is 4 *);
      @     ensures (* \result is <a,b,c,d> *);
      @*/
    /*@
    model public  non_null  JMLValueSequence removeItemAt(\bigint index)
        throws JMLSequenceException {
        if (0 <= index && index < length()) {
            JMLListValueNode new_list = theSeq.removeItemAt(index);
             assume new_list == null <==> int_length() == 1;
             assume !containsNull && new_list != null
                ==> !new_list.containsNull;
            
            return new JMLValueSequence(new_list, length()-1);
        } else {
            throw new
                JMLSequenceException("Invalid parameter to removeItemAt() "
                                     + "with index = " + index + "\n"
                                     + "   when sequence length = " + length());
        }
    }
    @*/

    /** Return a sequence like this, but without the element at the
     *  given zero-based index.
     *  @param index the zero-based index into the sequence.
     *  @exception JMLSequenceException if the index is out of range.
     * @see #itemAt(int)
     * @see #removeItemAt
     * @see #prefix
     * @see #removePrefix
     * @see #subsequence
     * @see #concat
     */
    /*@  public normal_behavior
      @    requires 0 <= index && index < int_length();
      @    ensures \result.equals(prefix(index).concat(removePrefix((int)(index+1))));
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with the item at position index removed *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < int_length());
      @    signals_only JMLSequenceException;
      @
      @ implies_that
      @    ensures !\result.containsNull <== !containsNull;
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and index is 1 *);
      @     ensures (* \result is <a,c,d,e> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and index is 4 *);
      @     ensures (* \result is <a,b,c,d> *);
      @*/
    public /*@ non_null @*/ JMLValueSequence removeItemAt(int index)
        throws JMLSequenceException {
        if (0 <= index && index < int_length()) {
            JMLListValueNode new_list = theSeq.removeItemAt(index);
            /*@ assume new_list == null <==> int_length() == 1;
              @ assume !containsNull && new_list != null
              @    ==> !new_list.containsNull;
              @*/
            return new JMLValueSequence(new_list, int_length()-1);
        } else {
            throw new
                JMLSequenceException("Invalid parameter to removeItemAt() "
                                     + "with index = " + index + "\n"
                                     + "   when sequence length = " + int_length());
        }
    }

    /** Return a sequence like this, but with item replacing the element at the
     *  given zero-based index.
     *  @param index the zero-based index into the sequence.
     *  @param item the item to put at index index
     *  @exception JMLSequenceException if the index is out of range.
     * @see #itemAt(int)
     * @see #replaceItemAt
     */
    /*@  public normal_behavior
      @    requires 0 <= index && index < length();
      @    ensures \result.equals(removeItemAt(index).insertBeforeIndex(index,
      @                                                                 item));
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with item replacing the one at position index *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < length());
      @    signals_only JMLSequenceException;
      @*/
    //@ implies_that
    //@    ensures item != null ==> \typeof(item) <: \result.elementType;
    //@    ensures !\result.containsNull <== !containsNull && item != null;
    /*@
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,e>, item is x and index is 1 *);
      @     ensures (* \result is <a,x,c,d,e> *);
      @*/
    /*@
    model public  non_null  JMLValueSequence
        replaceItemAt(\bigint index, JMLType item)
        throws JMLSequenceException {
        if (0 <= index && index < length()) {
            // replaceItemAt() clones item, if necessary
            JMLListValueNode new_list = theSeq.replaceItemAt(index, item);
             assume new_list == null <==> length() == 0;
            return new JMLValueSequence(new_list, length());
        } else {
            throw new
                JMLSequenceException("Invalid parameter to replaceItemAt() "
                                     + "with index = " + index + "\n"
                                     + "   when sequence length = " + length());
        }
    }  nowarn Post;
    @*/

    /** Return a sequence like this, but with item replacing the element at the
     *  given zero-based index.
     *  @param index the zero-based index into the sequence.
     *  @param item the item to put at index index
     *  @exception JMLSequenceException if the index is out of range.
     * @see #itemAt(int)
     * @see #replaceItemAt
     */
    /*@  public normal_behavior
      @    requires 0 <= index && index < int_length();
      @    ensures \result.equals(removeItemAt(index).insertBeforeIndex(index,
      @                                                                 item));
      @    ensures_redundantly 
      @           (* \result is the same as this,
      @              but with item replacing the one at position index *);
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= index && index < int_length());
      @    signals_only JMLSequenceException;
      @*/
    //@ implies_that
    //@    ensures item != null ==> \typeof(item) <: \result.elementType;
    //@    ensures !\result.containsNull <== !containsNull && item != null;
    /*@
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,e>, item is x and index is 1 *);
      @     ensures (* \result is <a,x,c,d,e> *);
      @*/
    public /*@ non_null @*/ JMLValueSequence
        replaceItemAt(int index, JMLType item)
        throws JMLSequenceException {
        if (0 <= index && index < int_length()) {
            // replaceItemAt() clones item, if necessary
            JMLListValueNode new_list = theSeq.replaceItemAt(index, item);
            //@ assume new_list == null <==> int_length() == 0;
            return new JMLValueSequence(new_list, int_length());
        } else {
            throw new
                JMLSequenceException("Invalid parameter to replaceItemAt() "
                                     + "with index = " + index + "\n"
                                     + "   when sequence length = " + int_length());
        }
    } //@ nowarn Post;

    /** Return a sequence containing all but the last element in this.
     *  @exception JMLSequenceException if this is empty.
     *  @see #prefix
     *  @see #first
     *  @see #last
     *  @see #trailer
     *  @see #subsequence
     */
    /*@  public normal_behavior
      @    requires int_length() >= 1;
      @    ensures \result.equals(removeItemAt((int)(int_length()-1)));
      @    ensures_redundantly \result.int_length() == int_length() - 1
      @          && (* \result is like this, but without the last item *);
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals (JMLSequenceException);
      @
      @ implies_that
      @    ensures !\result.containsNull <== !containsNull;
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d> *);
      @     ensures (* \result is <a,b,c> *);
      @*/
    public /*@ non_null @*/ JMLValueSequence header()
        throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried header() on empty sequence.");
        } else {
            JMLListValueNode new_list = theSeq.removeLast();
            //@ assume new_list == null <==> int_length() == 1;
            return new JMLValueSequence(new_list, int_length() - 1);
        }   
    } //@ nowarn Post;

    /** Return a sequence containing all but the first element in this.
     *  @exception JMLSequenceException if this is empty.
     *  @see #removePrefix
     *  @see #last
     *  @see #first
     *  @see #header
     *  @see #subsequence
     */
    /*@  public normal_behavior
      @    requires int_length() >= 1;
      @    ensures \result.equals(removePrefix(1));
      @    ensures_redundantly \result.int_length() == int_length() - 1
      @           && (* \result is like this, but without the first item *);
      @ also
      @  public exceptional_behavior
      @    requires int_length() == 0;
      @    signals (JMLSequenceException);
      @
      @ implies_that
      @    ensures !\result.containsNull <== !containsNull;
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d> *);
      @     ensures (* \result is <b,c,d> *);
      @*/
    public /*@ pure @*/ /*@ non_null @*/ JMLValueSequence trailer()
        throws JMLSequenceException {
        if (theSeq == null) {
            throw new JMLSequenceException("Tried trailer() on empty sequence.");
        } else {
            JMLListValueNode new_list = theSeq.next;
            //@ assume new_list == null <==> int_length() == 1;
            /*@ assume !new_list.containsNull
              @        <== new_list != null && !containsNull;
              @*/
            return new JMLValueSequence(new_list, int_length() - 1);
        }   
    }  


    /** Return a sequence like this, but with item put immediately after
     *  the given index.
     *  @param afterThisOne a zero-based index into the sequence, or -1.
     *  @param item the item to put after index afterThisOne
     *  @return if the index is in range
     *  @exception JMLSequenceException if the index is out of range.
     *  @see #insertBeforeIndex
     *  @see #insertFront
     *  @see #insertBack
     *  @see #removeItemAt
     */
    /*@ //FIXME, _ alsoIfValue _
      @  public normal_behavior
      @    requires -1 <= afterThisOne && afterThisOne < length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex((int)(afterThisOne + 1), item));
      @    ensures_redundantly 
      @          (* \result is the same sequence as this,
      @             but with item inserted after the index "afterThisOne" *);
      @ also
      @  public exceptional_behavior
      @    requires !(-1 <= afterThisOne && afterThisOne < length);
      @    signals (JMLSequenceException);
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c> and afterThisOne is 1 and item is d *);
      @     ensures (* \result is <a,b,d,c> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c> and afterThisOne is -1 and item is d *);
      @     ensures (* \result is <d,a,b,c> *);
      @*/
    /*@
    model public non_null JMLValueSequence insertAfterIndex(\bigint afterThisOne,
                                                             JMLType item) //FIXME, _ nonNullIfObj _ 
        throws JMLSequenceException, IllegalStateException
    {
        if (afterThisOne < -1 || afterThisOne >= length) {
            throw new JMLSequenceException("Invalid parameter to "
                                           + "insertAfterIndex() "
                                           + "with afterThisOne = " 
                                           + afterThisOne + "\n"
                                           + "   when sequence length = "
                                           + length);
        } else {
            return insertBeforeIndex(afterThisOne+1, item);
        } 
    } @*/


    /** Return a sequence like this, but with item put immediately after
     *  the given index.
     *  @param afterThisOne a zero-based index into the sequence, or -1.
     *  @param item the item to put after index afterThisOne
     *  @return if the index is in range
     *  @exception JMLSequenceException if the index is out of range.
     *  @see #insertBeforeIndex
     *  @see #insertFront
     *  @see #insertBack
     *  @see #removeItemAt
     */
    /*@ also
      @  public normal_behavior
      @    requires -1 <= afterThisOne && afterThisOne < length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex((int)(afterThisOne + 1), item));
      @    ensures_redundantly 
      @          (* \result is the same sequence as this,
      @             but with item inserted after the index "afterThisOne" *);
      @ also
      @  public exceptional_behavior
      @    requires !(-1 <= afterThisOne && afterThisOne < length);
      @    signals (JMLSequenceException);
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c> and afterThisOne is 1 and item is d *);
      @     ensures (* \result is <a,b,d,c> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c> and afterThisOne is -1 and item is d *);
      @     ensures (* \result is <d,a,b,c> *);
      @*/
    public /*@ non_null @*/ JMLValueSequence insertAfterIndex(int afterThisOne,
                                                             JMLType item)
        throws JMLSequenceException, IllegalStateException
    {
        if (afterThisOne < -1 || afterThisOne >= int_length()) {
            throw new JMLSequenceException("Invalid parameter to "
                                           + "insertAfterIndex() "
                                           + "with afterThisOne = " 
                                           + afterThisOne + "\n"
                                           + "   when sequence length = "
                                           + int_length());
        } else if (int_length() < Integer.MAX_VALUE) {
            return insertBeforeIndex(afterThisOne+1, item);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    }


    private static final String TOO_BIG_TO_INSERT
        = "Cannot insert into a sequence with Integer.MAX_VALUE elements.";

    /** Return a sequence like this, but with item put immediately
     *  before the given index.
     *  @param beforeThisOne a zero-based index into the sequence,
     *         or the length of this.
     *  @param item the item to put before index beforeThisOne
     *  @return if the index is in range
     *  @exception JMLSequenceException if the index is out of range.
     *  @see #insertAfterIndex
     *  @see #insertFront
     *  @see #insertBack
     *  @see #removeItemAt
     */
    /*@ //FIXME, _ alsoIfValue _
      @  public normal_behavior
      @    requires 0 <= beforeThisOne && beforeThisOne <= length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(
      @               prefix(beforeThisOne).
      @                  concat(new JMLValueSequence(item)).
      @                     concat(removePrefix(beforeThisOne))
      @            );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= beforeThisOne && beforeThisOne <= length);
      @    signals (JMLSequenceException);
      @*/
    /*@ 
      model public  
        non_null JMLValueSequence insertBeforeIndex(\bigint beforeThisOne, JMLType item)
        throws JMLSequenceException, IllegalStateException //FIXME, _ nonNullIfObj _
    {
        if (beforeThisOne < 0 || beforeThisOne > length) {
            throw new
                JMLSequenceException("Invalid parameter to insertBeforeIndex()"
                                     + " with beforeThisOne = " 
                                     + beforeThisOne + "\n"
                                     + "   when sequence length = " + length);
        } else if (theSeq == null) {
	  return new JMLValueSequence(item);
	} else {
	  // insertBefore() clones item, if necessary
	  JMLListValueNode new_list
	  = theSeq.insertBefore(beforeThisOne, item);
	  //@ assume new_list != null;
	  return new JMLValueSequence(new_list, int_length()+1);
	}
    }   nowarn NonNullResult;
    @*/

    /** Return a sequence like this, but with item put immediately
     *  before the given index.
     *  @param beforeThisOne a zero-based index into the sequence,
     *         or the length of this.
     *  @param item the item to put before index beforeThisOne
     *  @return if the index is in range
     *  @exception JMLSequenceException if the index is out of range.
     *  @see #insertAfterIndex
     *  @see #insertFront
     *  @see #insertBack
     *  @see #removeItemAt
     */
    /*@ also
      @  public normal_behavior
      @    requires 0 <= beforeThisOne && beforeThisOne <= length;
      @    requires length < Integer.MAX_VALUE;
      @    ensures \result.equals(
      @               prefix(beforeThisOne).
      @                  concat(new JMLValueSequence(item)).
      @                     concat(removePrefix(beforeThisOne))
      @            );
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= beforeThisOne && beforeThisOne <= length);
      @    signals (JMLSequenceException);
      @*/
    public /*@ non_null @*/
        JMLValueSequence insertBeforeIndex(int beforeThisOne, JMLType item)
        throws JMLSequenceException, IllegalStateException
    {
        if (beforeThisOne < 0 || beforeThisOne > int_length()) {
            throw new
                JMLSequenceException("Invalid parameter to insertBeforeIndex()"
                                     + " with beforeThisOne = " 
                                     + beforeThisOne + "\n"
                                     + "   when sequence length = " + int_length());
        } else if (int_length() < Integer.MAX_VALUE) {
            if (theSeq == null) {
                return new JMLValueSequence(item);
            } else {
                // insertBefore() clones item, if necessary
                JMLListValueNode new_list
                    = theSeq.insertBefore(beforeThisOne, item);
                //@ assume new_list != null;
                return new JMLValueSequence(new_list, int_length()+1);
            }
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    } //@ nowarn NonNullResult;

    /** Return a sequence like this, but with the given item put an the end.
     *  @param item the item to put at the end of the result.
     *  @return a sequence the elements of this sequence followed by item.
     *  @see #insertAfterIndex
     *  @see #insertBeforeIndex
     *  @see #insertFront
     *  @see #removeItemAt
     *  @see #header
     *  @see #last
     */
    /*@ also
      @  public normal_behavior
      @    requires int_length() < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex(int_length(), item));
      @    ensures_redundantly
      @        \result.int_length() == int_length() + 1
      @        && isProperPrefix(\result);
      @    ensures_redundantly 
      @           (* \result is the same sequence as this,
      @              but with item.clone() inserted at the back,
      @              after index int_length() - 1 *);
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c> and item is d *);
      @     ensures (* \result is <a,b,c,d> *);
      @*/
    public /*@ non_null @*/ JMLValueSequence insertBack(JMLType item)
        throws IllegalStateException
    {
        if (theSeq == null) {
            return new JMLValueSequence(item);
        } else if (int_length() < Integer.MAX_VALUE) {
            // append() clones item, if necessary
            return new JMLValueSequence(theSeq.append(item), int_length()+1);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    }

    /** Return a sequence like this, but with the given item put an the front.
     *  @param item the item to put at the front of the result.
     *  @return a sequence with item followed by the elements of this sequence.
     *  @see #insertAfterIndex
     *  @see #insertBeforeIndex
     *  @see #insertBack
     *  @see #removeItemAt
     *  @see #trailer
     *  @see #first
     */
    /*@ also
      @  public normal_behavior
      @    requires int_length() < Integer.MAX_VALUE;
      @    ensures \result.equals(insertBeforeIndex(0, item));
      @    ensures_redundantly
      @        \result.int_length() == int_length() + 1
      @        && \result.trailer().equals(this);
      @    ensures_redundantly 
      @          (* \result is the same sequence as this,
      @             but with item.clone() inserted at the front,
      @             before index 0 *);
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c> and item is d *);
      @     ensures (* \result is <d,a,b,c> *);
      @*/
    public /*@ pure @*/ /*@ non_null @*/ JMLValueSequence insertFront(JMLType item)
        throws IllegalStateException
    {
        if (theSeq == null) {
            return new JMLValueSequence(item);
        } else if (int_length() < Integer.MAX_VALUE) {
            return new JMLValueSequence(  // cons() clones item, if necessary
                                         JMLListValueNode.cons(item, theSeq),
                                         int_length()+1);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_INSERT);
        }
    }

    /** Returns a subsequence of this containing the elements beginning
     *   with index from (inclusive) and ending with index to (exclusive).
     *  @param from the inclusive, zero-based element of the first
     *  element in the subsequence.
     *  @param to the zero-based element of the first element that
     *  should not be in the subsequence.
     *  @exception JMLSequenceException if (from < 0 or from > to
     *  or to > length of this.
     *  @see #prefix
     *  @see #removePrefix
     *  @see #header
     *  @see #trailer
     *  @see #concat
     */
    /*@  public normal_behavior
      @    requires 0 <= from && from <= to && to <= length();
      @    ensures \result.equals(removePrefix(from).prefix((int)(to - from)));
      @    ensures_redundantly
      @           (* \result contains the elements of this beginning with
      @              index from (inclusive) and ending
      @              with index to (exclusive) *)
      @         && \result.length() == to - from;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= from && from <= to && to <= length());
      @    signals (JMLSequenceException);
      @
      @ implies_that
      @    ensures !\result.containsNull <== !containsNull;
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and from is 1 and to is 3 *);
      @     ensures (* \result is <b,c> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and from is 0 and to is 3 *);
      @     ensures (* \result is <a,b,c> *);
      @  also
      @   public normal_example
      @     requires from == to;
      @     ensures \result.isEmpty();
      @*/
    /*@
    model public  non_null  JMLValueSequence subsequence(\bigint from, \bigint to)
        throws JMLSequenceException {
        if (from < 0 || from > to || to > length()) {
            throw new JMLSequenceException("Invalid parameters to "
                                           + "subsequence() with from = " 
                                           + from + " and to = " + to + "\n"
                                           + "   " + "when sequence length = "
                                           + length());
        } else {
            if (theSeq == null) {
                return this;  // i.e., from == to == length() == 0
            } else {
                JMLListValueNode removedPrefix = theSeq.removePrefix(from);
                if (removedPrefix == null) {
                     assert from == length() && from == to;
                    return new JMLValueSequence();
                } else {
                    JMLListValueNode new_list = removedPrefix.prefix(to-from);
                     assume new_list == null <==> to == from;
                    return new JMLValueSequence(new_list, to - from);
                }
            }
        }
    }  nowarn Post;
    @*/

    /** Returns a subsequence of this containing the elements beginning
     *   with index from (inclusive) and ending with index to (exclusive).
     *  @param from the inclusive, zero-based element of the first
     *  element in the subsequence.
     *  @param to the zero-based element of the first element that
     *  should not be in the subsequence.
     *  @exception JMLSequenceException if (from < 0 or from > to
     *  or to > length of this.
     *  @see #prefix
     *  @see #removePrefix
     *  @see #header
     *  @see #trailer
     *  @see #concat
     */
    /*@  public normal_behavior
      @    requires 0 <= from && from <= to && to <= int_length();
      @    ensures \result.equals(removePrefix(from).prefix((int)(to - from)));
      @    ensures_redundantly
      @           (* \result contains the elements of this beginning with
      @              index from (inclusive) and ending
      @              with index to (exclusive) *)
      @         && \result.int_length() == to - from;
      @ also
      @  public exceptional_behavior
      @    requires !(0 <= from && from <= to && to <= int_length());
      @    signals (JMLSequenceException);
      @
      @ implies_that
      @    ensures !\result.containsNull <== !containsNull;
      @ for_example
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and from is 1 and to is 3 *);
      @     ensures (* \result is <b,c> *);
      @  also
      @   public normal_example
      @     requires (* this is <a,b,c,d,e> and from is 0 and to is 3 *);
      @     ensures (* \result is <a,b,c> *);
      @  also
      @   public normal_example
      @     requires from == to;
      @     ensures \result.isEmpty();
      @*/
    public /*@ non_null @*/ JMLValueSequence subsequence(int from, int to)
        throws JMLSequenceException {
        if (from < 0 || from > to || to > int_length()) {
            throw new JMLSequenceException("Invalid parameters to "
                                           + "subsequence() with from = " 
                                           + from + " and to = " + to + "\n"
                                           + "   " + "when sequence length = "
                                           + int_length());
        } else {
            if (theSeq == null) {
                return this;  // i.e., from == to == int_length() == 0
            } else {
                JMLListValueNode removedPrefix = theSeq.removePrefix(from);
                if (removedPrefix == null) {
                    //@ assert from == int_length() && from == to;
                    return new JMLValueSequence();
                } else {
                    JMLListValueNode new_list = removedPrefix.prefix(to-from);
                    //@ assume new_list == null <==> to == from;
                    return new JMLValueSequence(new_list, to - from);
                }
            }
        }
    } //@ nowarn Post;

    /** Return a new JMLValueBag containing all the elements of this.
     * @see #toSet()
     * @see #toArray()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall int i; 0 <= i && i < int_length();
      @                            \result.count(this.itemAt(i))
      @                             == this.count(this.itemAt(i)));
      @*/
    public /*@ non_null @*/ JMLValueBag toBag() {
        JMLValueBag ret = new JMLValueBag();
        JMLValueSequenceEnumerator elems = elements();
        while (elems.hasMoreElements()) {
            //@ assume elems.moreElements;
            Object o = elems.nextElement();
            JMLType e = (o == null ? null : (JMLType)  o);
            ret = ret.insert(e);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return a new JMLValueSet containing all the elements of this.
     * @see #toBag()
     * @see #toArray()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall JMLType o;; \result.has(o) == this.has(o));
      @*/
    public /*@ non_null @*/ JMLValueSet toSet() {
        JMLValueSet ret = new JMLValueSet();
        JMLValueSequenceEnumerator elems = elements();
        while (elems.hasMoreElements()) {
            //@ assume elems.moreElements;
            Object o = elems.nextElement();
            JMLType e = (o == null ? null : (JMLType)  o);
            ret = ret.insert(e);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return a new array containing all the elements of this in order.
     * @see #toSet()
     * @see #toBag()
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.length == int_length()
      @         && (\forall int i; 0 <= i && i < int_length();
      @                 (\result[i] == null ==> this.itemAt(i) == null)
      @              && (\result[i] != null ==>
      @                   \result[i].equals(this.itemAt(i))));
      @*/
    public /*@ non_null @*/ JMLType[] toArray() {
        JMLType[] ret = new JMLType[int_length()];
        JMLValueSequenceEnumerator elems = elements();
        int i = 0;
        //@ loop_invariant 0 <= i && i <= ret.length;
        while (elems.hasMoreElements()) {
            //@ assume elems.moreElements && i < ret.length;
            Object o = elems.nextElement();
            if (o == null) {
                ret[i] = null;
            } else {
                JMLType e = (JMLType)  o;
                ret[i] = (JMLType)  e.clone();
            }
            i++;
        }
        return ret;
    } //@ nowarn Exception;

    //********************** Tools Methods *********************************

    // The enumerator method and toString are of no value for writing
    // assertions in JML. They are included for the use of developers
    // of CASE tools based on JML, e.g., type checkers, assertion
    // evaluators, prototype generators, test tools, ... . They can
    // also be used in model programs in specifications.

    /** Return a enumerator for this.
     * @see #iterator()
     * @see #itemAt()
     */
    /*@  public normal_behavior
      @    ensures \fresh(\result) && (* \result is an enumerator for this *);
      @*/
    public /*@ non_null @*/ JMLValueSequenceEnumerator elements() {
        JMLValueSequenceEnumerator retValue 
            = new JMLValueSequenceEnumerator(this);
        return retValue;
    }  

    /** Returns an iterator over this sequence.
     * @see #elements()
     */
    /*@ also
      @    public normal_behavior
      @      ensures \fresh(\result)
      @          && \result.equals(new JMLEnumerationToIterator(elements()));
      @*/  
    public /*@ non_null @*/ JMLIterator iterator() {
        return new JMLEnumerationToIterator(elements());
    }  //@ nowarn Post;

    /** Return a string representation of this object.
     */
    /*@ also
      @  public normal_behavior
      @    ensures (* \result is a string representation of this *);
      @*/
    public /*@ non_null @*/ String toString() {
        String newStr = "(<";
        JMLListValueNode seqWalker = theSeq;
        boolean first = true;
        while (seqWalker != null) {
            if (!first) {
                newStr = newStr + ", ";
            }
            newStr = newStr + seqWalker.val;
            first = false;
            seqWalker = seqWalker.next;
        }
        return(newStr + ">)");
    }

    //exchange a value of a \bigint to BigInteger
    /*@ public static model pure BigInteger bigintToBigInteger(\bigint biValue) {
      @ BigInteger oBiValue;
      @
      @ if(biValue > Long.MAX_VALUE) {
      @     oBiValue = BigInteger.valueOf(Long.MAX_VALUE);
      @     \bigint biInterval = biValue - Long.MAX_VALUE;
      @     while(biInterval > Long.MAX_VALUE) {
      @         oBiValue = oBiValue.add(BigInteger.valueOf(Long.MAX_VALUE));
      @         biInterval =  biInterval - Long.MAX_VALUE;
      @     }
      @     oBiValue = oBiValue.add(BigInteger.valueOf((long)biInterval));
      @ } else {
      @     oBiValue = BigInteger.valueOf((long)biValue);
      @ }
      @
      @ return oBiValue;
      @ }
      @*/

    //exchange a value of a BigInteger to \bigint
    /*@ public normal_behavior
        requires oBi.equals(BigInteger.ZERO);
        ensures \result == (\bigint)0;
     */
    /*@ public static model pure \bigint bigIntegerToBigint(BigInteger oBi) {
      @ \bigint valAsBigint;
      @
      @ if(oBi.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) > 0) {
      @     valAsBigint = Long.MAX_VALUE;
      @     BigInteger bigintInterval = oBi.subtract(BigInteger.valueOf(Long.MAX_VALUE));
      @     while(bigintInterval.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) > 0) {
      @         valAsBigint = valAsBigint + Long.MAX_VALUE;
      @         bigintInterval =  bigintInterval.subtract(BigInteger.valueOf(Long.MAX_VALUE));
      @     }
      @     valAsBigint = valAsBigint + bigintInterval.longValue();
      @ } else {
      @     valAsBigint = oBi.longValue();
      @ }
      @
      @ return valAsBigint;
      @ }
      @*/

}
