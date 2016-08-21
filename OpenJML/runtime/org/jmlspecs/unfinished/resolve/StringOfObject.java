// @(#)$Id: StringOfObject.java,v 1.33 2006/02/17 01:21:47 chalin Exp $

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

package org.jmlspecs.unfinished.resolve;

import java.util.Collection;
import java.util.Iterator;
import org.jmlspecs.models.*;

/** Sequences of non-null object identities.  Objects in the sequence
 *  are not cloned coming in or going out, and this type uses "==" to
 *  compare object identities.
 *
 *  <p>The names in this type are based prnimarily
 *  on the RESOLVE design, but are also chosen to be understandable to
 *  someone familiar with {@link java.util.Collection}.  However, note that
 *  none of the operations does any mutation.
 *
 *  <p>Many of the specifications are translated from William Ogden's
 *  notes for CIS 680 at Ohio State University.  (Thanks Bill!)  This
 *  is especially true for the ones specified recursively.  Specifications
 *  written using the {@link #size} and {@link #get} operations are an
 *  alternative, and often given in the redundant parts.
 *
 * @version $Revision: 1.33 $
 * @author Gary T. Leavens
 * @see org.jmlspecs.models.JMLObjectSequence
 * @see org.jmlspecs.models.JMLCollection
 * @see TotallyOrderedCompareTo
 */
public /*@ pure @*/ class StringOfObject implements JMLCollection
{
    //@ public invariant owner == null;

    //@ public invariant !containsNull;

    /*@ public invariant
      @           (\forall Object o; o != null && has(o);
      @                                 \typeof(o) <: elementType);
      @*/

    /** The sequence of objects that represent this string of objects. */
    protected final /*@ spec_public non_null @*/ JMLObjectSequence elements;
    //@                                         in objectState;

    //@ protected invariant !elements.containsNull;

    // ********************** constructors ************************

    /** Initialize this object to be empty string of objects.
     * @see #EMPTY
     * @see #StringOfObject(Object)
     */
    /*@ public normal_behavior
      @   assignable objectState, owner, containsNull, elementType;
      @   ensures elements.isEmpty();
      @*/
    public StringOfObject () {
        //@ set owner = null;
        //@ set containsNull = false;
        //@ set elementType = \type(Object);
        elements = new JMLObjectSequence();
    }

    /** Message used in exceptions. */
    private static final String ILLEGAL_ARG_MSG 
        = "Attempt to add null to a StringOfObject";

    /** Initialize this object to string containing just the given object.
     * @see #StringOfObject()
     * @see #singleton(Object)
     */
    /*@ public normal_behavior
      @   requires elem != null;
      @   assignable objectState, owner, containsNull, elementType;
      @   ensures elements.equals(new JMLObjectSequence(elem));
      @*/
    //@ implies_that
    //@    requires elem != null;
    public StringOfObject (/*@ non_null @*/ Object elem)
        throws IllegalArgumentException
    {
        //@ set owner = null;
        //@ set containsNull = false;
        //@ set elementType = \typeof(elem);
        if (elem != null) {
            elements = new JMLObjectSequence(elem);
            //@ assume !elements.containsNull;
        } else {
            throw new IllegalArgumentException(ILLEGAL_ARG_MSG);
        }
    }

    /** Initialize this object from the given representation.
     */
    /*@ protected normal_behavior
      @   requires os != null && !os.containsNull && os.owner == null;
      @   assignable objectState, owner, containsNull, elementType;
      @   ensures elements != null && elements.equals(os);
      @*/
    //@ implies_that
    //@    requires os != null && !os.containsNull;
    protected StringOfObject (/*@ non_null @*/ JMLObjectSequence os)
        throws IllegalArgumentException
    {
        //@ set owner = null;
        //@ set containsNull = false;
        //@ set elementType = os.elementType;
        elements = os;
    }

    // *************** Static Constants and Factory Methods ************

    /** The empty string of objects.
     * @see #StringOfObject()
     */
    public static final /*@ non_null @*/ StringOfObject EMPTY
        = new StringOfObject();

    //@ public invariant_redundantly EMPTY != null && EMPTY.isEmpty();
    //@ public constraint_redundantly EMPTY == \old(EMPTY);

    /** Make a singleton string of objects containing just the given object.
     * @see #StringOfObject(Object)
     */
    /*@ public normal_behavior
      @    requires elem != null;
      @    ensures \result != null
      @        && \result.int_size() == 1 && \result.get(0) == elem;
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        StringOfObject singleton(/*@ non_null @*/ Object elem)
        throws IllegalArgumentException
    {
        return new StringOfObject(elem);
    }

    /** Extend the given string by placing the given element at the end.
     * @see #ext(Object)
     * @see #add(Object)
     * @see #addFront(Object)
     * @see #addAfterIndex
     * @see #addBeforeIndex
     */
    /*@ public normal_behavior
      @   requires s != null && elem != null;
      @   ensures \result != null
      @        && \result.elements.equals(s.elements.insertBack(elem));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ 
        StringOfObject ext(/*@ non_null @*/ StringOfObject s,
                           /*@ non_null @*/ Object elem)
        throws IllegalArgumentException
    {
        return s.ext(elem);
    }

    /** Make an array of objects into a string.
     * @see #from(Collection)
     * @see #addAll(Object[])
     */
    /*@ public normal_behavior
      @   requires \nonnullelements(a);
      @   ensures \result != null && \result.equals(EMPTY.addAll(a));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ 
        StringOfObject from(/*@ non_null @*/ Object[] a)
        throws IllegalArgumentException
    {
        return EMPTY.addAll(a);
    }

    /** Make a collection into a string.
     * @see #from(Object[])
     * @see #addAll(Collection)
     */
    /*@ public normal_behavior
      @   requires c != null && !c.contains(null);
      @   ensures \result != null && \result.equals(EMPTY.addAll(c));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ 
        StringOfObject from(/*@ non_null @*/ Collection c)
        throws IllegalArgumentException
    {
        return EMPTY.addAll(c);
    }

    /** Compose all the elements of <kbd>a</kbd> in order.
     * @see #productFrom(StringOfObject[], int)
     * @see #productFromTo(StringOfObject[], int, int)
     * @see #composedWith(StringOfObject)
     */
    /*@ public normal_behavior
      @   requires \nonnullelements(a);
      @   ensures \result.equals(productFrom(a, 0));
      @*/
    //@ implies_that
    //@   requires \nonnullelements(a);
    public static /*@ pure @*/ /*@ non_null @*/ 
        StringOfObject product(/*@ non_null @*/ StringOfObject[] a)
    {
        return productFrom(a, 0);
    }

    /** Compose all the elements of a in order, starting at the given index.
     * @see #productFrom(StringOfObject[])
     * @see #productFromTo(StringOfObject[], int, int)
     * @see #composedWith(StringOfObject)
     */
    /*@ public normal_behavior
      @   requires \nonnullelements(a)
      @         && 0 <= fromIndex && fromIndex <= a.length;
      @   ensures \result.equals(productFromTo(a, fromIndex, a.length));
      @*/
    //@ implies_that
    /*@   requires \nonnullelements(a)
      @         && a != null && 0 <= fromIndex && fromIndex <= a.length;
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ 
        StringOfObject productFrom(/*@ non_null @*/ StringOfObject[] a,
                                   int fromIndex)
    {
        return productFromTo(a, fromIndex, a.length);
    }

    /** Compose all the elements of a in order, starting with
     *  <kbd>fromIndex</kbd>, and including elements up to but not
     *  including <kbd>toIndex</kbd>.
     * @param fromIndex the index of the first string of elements to
     * compose with.
     * @param toIndex one past the index of the elements to compose with.
     * @see #productFrom(StringOfObject[], int)
     * @see #productFromTo(StringOfObject[], int, int)
     * @see #composedWith(StringOfObject)
     */
    /*@ public normal_behavior
      @   requires \nonnullelements(a)
      @         && a != null && 0 <= fromIndex && fromIndex <= toIndex
      @         && toIndex <= a.length;
      @   {|
      @      requires fromIndex == toIndex;
      @      ensures \result != null && \result.isEmpty();
      @   also
      @      requires fromIndex < toIndex;
      @      ensures \result != null
      @        && \result.equals(new StringOfObject(a[fromIndex])
      @                           .concat(productFromTo(a, (int)(fromIndex+1),
      @                                                 toIndex)));
      @   |}
      @*/
    //@ implies_that
    /*@   requires \nonnullelements(a)
      @         && a != null && 0 <= fromIndex && fromIndex <= toIndex
      @         && toIndex <= a.length;
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ 
        StringOfObject productFromTo(/*@ non_null @*/ StringOfObject[] a,
                                     int fromIndex, int toIndex) {
        if (fromIndex == toIndex) {
            return EMPTY;
        } else {
            //@ assume a != null;
            //@ assert fromIndex < a.length;
            return new StringOfObject(a[fromIndex])
                .concat(productFromTo(a, fromIndex+1, toIndex));
        }
    } //@ nowarn Exception;

    // ***************** Observers ********************

    /** Return the element in the string at the given index.
     */
    /*@   public normal_behavior
      @     requires 0 <= index && index < elements.int_size();
      @     ensures \result == elements.itemAt(index);
      @ also
      @   public exceptional_behavior
      @     requires !(0 <= index && index < elements.int_size());
      @     signals_only IndexOutOfBoundsException;
      @ for_example
      @   public normal_example
      @     forall Object x;
      @     requires this.equals(new StringOfObject(x)) && index == 0;
      @     ensures \result == x;
      @ also
      @   public exceptional_example
      @     requires this.isEmpty();
      @     signals_only IndexOutOfBoundsException;
      @*/
    public /*@ non_null @*/ Object get(int index)
        throws IndexOutOfBoundsException
    {
        return elements.itemAt(index);
    } //@ nowarn NonNullResult;

    /** Tell the size of this string.
     * @see #length()
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result == elements.int_size();
      @     ensures_redundantly \result >= 0;
      @ implies_that
      @   public normal_behavior
      @     requires isEmpty();
      @     ensures \result == 0;
      @ also
      @   public normal_behavior
      @     forall Object x;
      @     forall StringOfObject beta;
      @     requires beta != null && this.equals(beta.ext(x));
      @     ensures \result == beta.int_size() + 1;
      @*/
    public int int_size() {
        return elements.int_size();
    }

    /** Tell the length (= size) of this string.
     * @see #int_size()
     */
    /*@ public normal_behavior
      @   ensures \result == elements.int_size();
      @   ensures_redundantly \result == int_size();
      @ implies_that
      @   public normal_behavior
      @     requires isEmpty();
      @     ensures \result == 0;
      @*/
    public int length() {
        return int_size();
    }

    /** Extend a string with a new element at the end.
     * @see #ext(StringOfObject, Object)
     * @see #add(Object)
     * @see #addFront(Object)
     * @see #addAfterIndex
     * @see #addBeforeIndex
     */
    /*@ public normal_behavior
      @   requires elem != null;
      @   ensures \result != null
      @        && \result.elements.equals(this.elements.insertBack(elem));
      @ implies_that
      @   public normal_behavior
      @     ensures \result != null && \result.int_size() == int_size() + 1
      @          && (\forall int i; 0 <= i && i < int_size();
      @                             \result.get(i) == this.get(i))
      @          && \result.get(this.int_size()) == elem;
      @ for_example
      @   public normal_example
      @     requires this.equals(EMPTY);
      @     ensures \result != null
      @          && \result.equals(new StringOfObject(elem));
      @ also
      @   public normal_example
      @     forall Object x;
      @     requires this.equals(new StringOfObject(x));
      @     ensures \result != null && \result.int_size() == 2
      @          && \result.get(0) == x && \result.get(1) == elem;
      @*/
    public /*@ non_null @*/ StringOfObject ext(/*@ non_null @*/ Object elem)
        throws IllegalArgumentException
    {
        if (elem != null) {
            return new StringOfObject(elements.insertBack(elem));//@ nowarn Pre;
        } else {
            throw new IllegalArgumentException(ILLEGAL_ARG_MSG);
        }
    } //@ nowarn Exception;

    /** Add an element to a string at the end. This is a synonym for ext.
     * @see #ext(Object)
     * @see #ext(StringOfObject, Object)
     * @see #addFront(Object)
     * @see #addAfterIndex
     * @see #addBeforeIndex
     */
    /*@ public normal_behavior
      @   requires elem != null;
      @   ensures \result != null && \result.equals(this.ext(elem));
      @*/
    public /*@ non_null @*/ StringOfObject add(/*@ non_null @*/ Object elem)
        throws IllegalArgumentException
    {
        return ext(elem);
    }

    /** Add an element to a string at the front.
     * @see #add(Object)
     * @see #ext(Object)
     * @see #ext(StringOfObject, Object)
     * @see #addAfterIndex
     * @see #addBeforeIndex
     */
    /*@ public normal_behavior
      @   ensures \result != null
      @        && \result.elements.equals(this.elements.insertFront(elem));
      @ implies_that
      @   public normal_behavior
      @     ensures \result != null && \result.int_size() == int_size() + 1
      @          && \result.get(0) == elem
      @          && (\forall int i; 0 <= i && i < int_size();
      @                             \result.get((int)(i+1)) == this.get(i));
      @ for_example
      @   public normal_example
      @     requires this.equals(EMPTY);
      @     ensures \result != null
      @          && \result.equals(new StringOfObject(elem));
      @ also
      @   public normal_example
      @     forall Object x;
      @     requires this.equals(new StringOfObject(x));
      @     ensures \result != null && \result.int_size() == 2
      @          && \result.get(0) == elem && \result.get(1) == x;
      @*/
    public /*@ non_null @*/ 
        StringOfObject addFront(/*@ non_null @*/ Object elem)
        throws IllegalArgumentException
    {
        if (elem != null) {
            return new StringOfObject(elements.insertFront(elem)); //@ nowarn Pre;
        } else {
            throw new IllegalArgumentException(ILLEGAL_ARG_MSG);
        }
    }  //@ nowarn Exception;

    /** Add an element to a string after the given index.
     * @see #addBeforeIndex
     * @see #addFront(Object)
     * @see #add(Object)
     * @see #ext(Object)
     * @see #ext(StringOfObject, Object)
     */
    /*@   public normal_behavior
      @     requires -1 <= afterThisOne && afterThisOne < int_size();
      @     ensures \result != null
      @       && \result.elements.equals(
      @             this.elements.insertAfterIndex(afterThisOne,elem));
      @ also
      @   public exceptional_behavior
      @     requires !(-1 <= afterThisOne && afterThisOne < int_size());
      @     signals_only IndexOutOfBoundsException;
      @ for_example
      @   public normal_example
      @     forall Object x;
      @     requires this.equals(new StringOfObject(x)) && afterThisOne == -1;
      @     ensures \result != null && \result.int_size() == 2
      @          && \result.get(0) == elem && \result.get(1) == x;
      @ also
      @   public normal_example
      @     forall Object x;
      @     requires this.equals(new StringOfObject(x)) && afterThisOne == 0;
      @     ensures \result != null && \result.int_size() == 2
      @          && \result.get(0) == x && \result.get(1) == elem;
      @*/
    public /*@ non_null @*/ 
        StringOfObject addAfterIndex(int afterThisOne,
                                     /*@ non_null @*/ Object elem)
        throws IndexOutOfBoundsException, IllegalArgumentException
    {
        if (elem != null) {
            JMLObjectSequence os
                = elements.insertAfterIndex(afterThisOne,elem); 
            //@ assume os != null && !os.containsNull;
            return new StringOfObject(os);
        } else {
            throw new IllegalArgumentException(ILLEGAL_ARG_MSG);
        }
    } //@ nowarn Exception;

    /** Add an element to a string before the given index.
     * @see #addAfterIndex
     * @see #addFront(Object)
     * @see #add(Object)
     * @see #ext(Object)
     * @see #ext(StringOfObject, Object)
     */
    /*@   public normal_behavior
      @     requires 0 <= beforeThisOne && beforeThisOne <= int_size();
      @     ensures \result != null
      @       && \result.elements.equals(
      @             this.elements.insertBeforeIndex(beforeThisOne,elem));
      @ also
      @   public exceptional_behavior
      @     requires !(0 <= beforeThisOne && beforeThisOne <= int_size());
      @     signals_only IndexOutOfBoundsException;
      @ for_example
      @   public normal_example
      @     forall Object x;
      @     requires this.equals(new StringOfObject(x)) && beforeThisOne == 0;
      @     ensures \result != null && \result.int_size() == 2
      @          && \result.get(0) == elem && \result.get(1) == x;
      @ also
      @   public normal_example
      @     forall Object x;
      @     requires this.equals(new StringOfObject(x)) && beforeThisOne == 1;
      @     ensures \result != null && \result.int_size() == 2
      @          && \result.get(0) == x && \result.get(1) == elem;
      @*/
    public /*@ non_null @*/ 
        StringOfObject addBeforeIndex(int beforeThisOne,
                                      /*@ non_null @*/ Object elem)
        throws IndexOutOfBoundsException, IllegalArgumentException
    {
        if (elem != null) {
            JMLObjectSequence os
                = elements.insertBeforeIndex(beforeThisOne,elem);
            //@ assume os != null && !os.containsNull;
            return new StringOfObject(os);
        } else {
            throw new IllegalArgumentException(ILLEGAL_ARG_MSG);
        }
    } //@ nowarn Exception;

    /** Concatenate this with s.
     * @see #composedWith
     */
    /*@ public normal_behavior
      @   requires s != null;
      @   {|
      @      requires s.isEmpty();
      @      ensures \result != null && \result.equals(this);
      @   also
      @      requires !s.isEmpty();
      @      ensures \result != null
      @           && (\forall StringOfObject beta; beta != null;
      @               (\forall Object x; s.equals(beta.ext(x));
      @                 \result.equals(this.concat(beta).ext(x))));
      @   |}
      @*/
    public /*@ non_null @*/ 
        StringOfObject concat(/*@ non_null @*/ StringOfObject s)
    {
        return new StringOfObject(elements.concat(s.elements));
    } //@ nowarn Exception;

    /** Compose this with s. This is a synonym for concat.
     * @see #concat
     */
    /*@ public normal_behavior
      @   requires s != null;
      @   ensures \result != null && \result.equals(concat(s));
      @*/
    public /*@ non_null @*/
        StringOfObject composedWith(/*@ non_null @*/ StringOfObject s)
    {
        return concat(s);
    }

    /** Add all the elements of c, at the end of this string, in the
     * order determined by c's iterator.
     * @see #addAll(Object[])
     * @see #from(Collection)
     */
    /*@ public normal_behavior
      @   requires c != null;
      @   ensures \result != null && \result.int_size() == this.int_size() + c.size()
      @         && (\forall int i; 0 <= i && i < \result.int_size();
      @               (i < this.int_size() ==> \result.get(i) == this.get(i))
      @               && (this.int_size() <= i
      @                    ==> \result.get(i)
      @                         == c.iterator().nthNextElement((int)(i - int_size()))));
      @ implies_that
      @   public normal_behavior
      @     requires c != null;
      @     ensures \result.equals(this);
      @*/
    public /*@ non_null @*/
        StringOfObject addAll(/*@ non_null @*/ Collection c)
        throws IllegalArgumentException
    {
        //@ assume c != null;
        JMLObjectSequence res = elements;
        Iterator i = c.iterator();
        //@ loop_invariant !res.containsNull;
        while (i.hasNext()) { //@ nowarn LoopInv;
            Object o = i.next();
            if (o != null) {
                res = res.insertBack(o);
            } else {
                throw new IllegalArgumentException(ILLEGAL_ARG_MSG);
            }
        }
        return new StringOfObject(res);
    } //@ nowarn Exception;

    /** Add all the elements of c at the end of this string, in order
     * from the smallest to the largest index.
     * @see #addAll(Collection)
     */
    /*@ public normal_behavior
      @   requires \nonnullelements(c);
      @   ensures \result != null && \result.int_size() == this.int_size() + c.length
      @         && (\forall int i; 0 <= i && i < \result.int_size();
      @               (i < this.int_size() ==> \result.get(i) == this.get(i))
      @               && (this.int_size() <= i
      @                    ==> \result.get(i) == c[(int)(i - this.int_size())]));
      @*/
    public /*@ non_null @*/
        StringOfObject addAll(/*@ non_null @*/ Object[] c)
        throws IllegalArgumentException
    {
        //@ assume c != null;
        JMLObjectSequence res = elements;
        //@ loop_invariant !res.containsNull && 0 <= i && i <= c.length;
        //@ decreasing c.length - i;
        for (int i = 0; i < c.length; i++) { //@ nowarn LoopInv;
            Object o = c[i];
            if (o != null) {
                res = res.insertBack(o);
            } else {
                throw new IllegalArgumentException(ILLEGAL_ARG_MSG);
            }
        }
        return new StringOfObject(res);
    } //@ nowarn Exception;

    /** Return the reverse of the string.  That is, the same string
     * with the elements in the opposite order.
     * @see #reverse
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && \result.elements.equals(elements.reverse());
      @ implies_that
      @   public normal_behavior
      @     ensures \result != null
      @         && \result.int_size() == this.int_size()
      @         && (\forall int i; 0 <= i && i < this.int_size();
      @                            this.get(i) == \result.get((int)(this.int_size()-i)));
      @ also
      @   public normal_behavior
      @     requires elements.isEmpty();
      @     ensures \result != null && \result.equals(this);
      @     ensures \result != null && \result.isEmpty();
      @ also
      @   public normal_behavior
      @     forall StringOfObject alpha;
      @     forall Object x;
      @     requires !elements.isEmpty();
      @     ensures \result != null
      @           && (alpha != null && this.equals(alpha.ext(x))
      @              ==> \result.equals(singleton(x).concat(alpha.rev())));
      @*/
    public /*@ non_null @*/ StringOfObject rev() {
        return new StringOfObject(elements.reverse());
    } //@ nowarn Exception;

    /** Return the reverse of the string.  That is, the same string
     * with the elements in the opposite order.
     * @see #rev
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.equals(this.rev());
      @*/
    public /*@ non_null @*/ StringOfObject reverse() {
        return rev();
    }

    /** Compose this string with itself the given number of times.
     * @see #composedWith
     */
    /*@   public normal_behavior
      @     requires n >= 0;
      @     {|
      @        requires n == 0;
      @        ensures \result != null && \result.isEmpty();
      @     also
      @        requires n > 0;
      @        ensures \result != null
      @           && \result.equals(this.pow((int)(n-1)).concat(this));
      @     |}
      @*/
    public /*@ non_null @*/ StringOfObject pow(int n)
        throws IllegalArgumentException
    {
        if (n < 0) {
            throw new IllegalArgumentException("Negative argument"
                                               + " to StringOfObejct.pow");
        }
        JMLObjectSequence ret = JMLObjectSequence.EMPTY;
        //@ loop_invariant n >= 0 && ret != null && !ret.containsNull;
        //@ decreases n;
        while (n > 0) { //@ nowarn LoopInv;
            ret = ret.concat(elements);
            n--;
        }
        //@ assume ret != null && !ret.containsNull;
        return new StringOfObject(ret);
    }

    // *************** Comparison Operations ***************************

    /** Tell if this object is equal to the given argument.
     * @see #compareTo(Object)
     * @see #compareTo(StringOfObject)
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result
      @          ==> x != null && x instanceof StringOfObject
      @              && int_size() == ((StringOfObject)x).int_size()
      @              && (\forall int i; 0 <= i && i < int_size();
      @                               get(i) == ((StringOfObject)x).get(i));
      @*/
    public boolean equals(/*@ nullable @*/ Object x) {
        if (x == null || !(x instanceof StringOfObject)) {
            return false;
        } else {
            return elements.equals(((StringOfObject)x).elements);
        }
    }

    public Object clone() {
        return this;
    }

    /** Tell how many times the given object appears in this string.
     */
    /*@ public normal_behavior
      @ {|
      @    requires isEmpty();
      @    ensures \result == 0;
      @ also
      @    forall StringOfObject alpha;
      @    requires alpha != null && this.equals(alpha.ext(y));
      @    ensures \result == alpha.occurs_ct(y) + 1;
      @ also
      @    forall StringOfObject alpha;
      @    forall Object x;
      @    requires alpha != null && this.equals(alpha.ext(x))
      @             && x != y;
      @    ensures \result == alpha.occurs_ct(y);
      @ |}
      @ implies_that
      @   public normal_behavior
      @     ensures \result 
      @             == (\num_of int i; 0 <= i && i < int_size(); get(i) == y);
      @                                     
      @*/
    public int occurs_ct(Object y) {
        return elements.count(y);
    }

    // specification and documentation inherited
    public boolean has(/*@ nullable @*/ Object elem) {
        return elements.has(elem);
    }

    /** Tell whether this string is empty.
     * @see #int_size()
     * @see #length()
     */
    /*@ public normal_behavior
      @   ensures \result <==> elements.isEmpty();
      @   ensures_redundantly \result <==> this.equals(EMPTY);
      @*/
    public boolean isEmpty() {
        return elements.isEmpty();
    }

    // specification and documentation inherited
    public int hashCode() {
        return elements.hashCode();
    }

    // specification and documentation inherited
    public String toString() {
        return elements.toString();
    }

    /** Return an iterator for this string of objects.
     * @see #elements()
     */
    public JMLIterator iterator() {
        return elements.iterator();
    } //@ nowarn Post;

    /** Return an enumerator for this string of objects.
     * @see #iterator()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && elements.equals(\result.uniteratedElems);
      @*/
    public JMLObjectSequenceEnumerator elements() {
        return elements.elements();
    }

    /** Tell whether this string occurs as a prefix of the given
     * argument string.
     * @see #isProperPrefix
     * @see #isSuffix
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @            (\exists StringOfObject s; s != null;
      @                                       this.concat(s).equals(s2));
      @    ensures_redundantly \result <==> elements.isPrefix(s2.elements);
      @*/
    public boolean isPrefix(/*@ non_null @*/ StringOfObject s2) {
        return elements.isPrefix(s2.elements);
    }

    /** Tell whether this string occurs as a proper prefix of the given
     * argument string.
     * @see #isPrefix
     * @see #isProperSuffix
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @            (\exists StringOfObject s; s != null && s.int_size() > 0;
      @                                          this.concat(s).equals(s2));
      @    ensures_redundantly \result
      @            <==> elements.isProperPrefix(s2.elements);
      @*/
    public boolean isProperPrefix(/*@ non_null @*/ StringOfObject s2) {
        return elements.isProperPrefix(s2.elements);
    }

    /** Tell whether this string occurs as a proper suffix of the given
     * argument string.
     * @see #isSuffix
     * @see #isProperPrefix
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @            (\exists StringOfObject r; r != null && r.int_size() > 0;
      @                                          r.concat(this).equals(s2));
      @    ensures_redundantly \result
      @            <==> elements.isProperSuffix(s2.elements);
      @*/
    public boolean isProperSuffix(/*@ non_null @*/ StringOfObject s2) {
        return elements.isProperSuffix(s2.elements);
    }

    /** Tell whether this string occurs as a suffix of the given
     * argument string.
     * @see #isProperSuffix
     * @see #isPrefix
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @            (\exists StringOfObject r; r != null;
      @                                          r.concat(this).equals(s2));
      @    ensures_redundantly \result <==> elements.isSuffix(s2.elements);
      @*/
    public boolean isSuffix(/*@ non_null @*/ StringOfObject s2) {
        return elements.isSuffix(s2.elements);
    }

}
