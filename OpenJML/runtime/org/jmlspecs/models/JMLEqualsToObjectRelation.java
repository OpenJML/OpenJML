// @(#)$Id: JMLRelation.java-generic,v 1.52 2006/02/17 01:21:47 chalin Exp $

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

import java.util.Enumeration;

/** Binary relations (or set-valued functions) from non-null elements
 *  of {@link Object} to non-null elements of {@link
 *  Object}.  The first type, <kbd>Object</kbd>, is called
 *  the domain type of the relation; the second type,
 *  <kbd>Object</kbd>, is called the range type of the relation.
 *  A relation can be seen as a set of pairs, of form <em>(dv,
 *  rv)</em>, consisting of an element of the domain type,
 *  <em>dv</em>, and an element of the range type, <em>rv</em>.
 *  Alternatively, it can be seen as a set-valued function that
 *  relates each element of the domain type to some set of elements of
 *  the range type (a {@link JMLObjectSet}).
 *
 *  <p> This type considers elements <kbd>val</kbd> and <kbd>dv<kbd>
 *  of the domain type, to be distinct just when
 *  <kbd>!val.equals(dv)</kbd>.  It considers elements of
 *  <kbd>r</kbd> and <kbd>rv</kbd> of the range type to be distinct
 *  just when <kbd>r != rv</kbd>.  Cloning takes place for
 *  the domain or range elements if the corresponding domain or range
 *  type is {@link JMLType}.
 *
 * @version $Revision: 1.52 $
 * @author Gary T. Leavens
 * @author Clyde Ruby
 * @see JMLCollection
 * @see JMLType
 * @see JMLEqualsToObjectMap
 * @see JMLEqualsToObjectRelationEnumerator
 * @see JMLEqualsToObjectRelationImageEnumerator
 * @see JMLValueSet
 * @see JMLObjectSet
 * @see JMLObjectToObjectRelation
 * @see JMLValueToObjectRelation
 * @see JMLObjectToValueRelation
 * @see JMLValueToValueRelation
 */
//-@ immutable
public /*@ pure @*/ class JMLEqualsToObjectRelation
    implements JMLCollection {

    /** The set of pairs of keys and values conceptually contained in
     * this object.
     */
    //@ public model JMLValueSet theRelation;
    /*@ public invariant
      @      (\forall Object obj; theRelation.has((JMLType)obj);
      @            obj != null
      @         && obj instanceof JMLEqualsObjectPair
      @         && ((JMLEqualsObjectPair)obj).key != null
      @         && ((JMLEqualsObjectPair)obj).value != null);
      @ public invariant_redundantly
      @      (* Every element of 'theRelation'is a JMLEqualsObjectPair
      @         whose key and value are not null *);
      @*/

    //@ public invariant elementType == \type(JMLEqualsObjectPair);

    //@ public invariant !containsNull;

    /** The set of elements in the domain of this relation.
     */
    protected final /*@ non_null @*/ JMLEqualsSet domain_;
    //@                                             in theRelation;

    /** The set representing the image pairs in the relation.  The
     * elements of this set are JMLEqualsValuePairs, which are all
     * non-null.  Each such pair has a key which is an element in
     * domain_ and a value which is a JMLObjectSet containing all of
     * the elements that the key of the pair is related to.
     */
    protected final /*@ non_null @*/ JMLValueSet imagePairSet_;
    //@                                             in theRelation;

    /** The size (number of pairs) of this relation.
     */
    protected final int size_;
    //@                  in theRelation;

    //@ protected represents theRelation <- toSet();

    /*@ protected invariant
      @     imagePairSet_.int_size() == domain_.int_size()
      @    && (\forall Object dv; dv != null && domain_.has(dv);
      @          imagePairSet_
      @            .has(new JMLEqualsValuePair(dv, elementImage(dv))));
      @*/
    //@ protected invariant_redundantly imagePairSet_ == imagePairSet();

    //@ protected invariant size_ == theRelation.int_size();
    //@ protected invariant size_ >= 0;

    //@ public    invariant owner == null;

    //************************* Constructors ********************************

    /** Initialize this to be an empty relation. That is, the value is
     * an empty set of pairs.
     * @see #EMPTY
     */
    /*@  public normal_behavior
      @    assignable theRelation, owner, elementType, containsNull;
      @    ensures theRelation.equals(new JMLValueSet());
      @    ensures_redundantly theRelation.isEmpty();
      @*/
    public JMLEqualsToObjectRelation()
    {
        //@ set owner = null;
        //@ set containsNull = false;
        //@ set elementType = \type(JMLEqualsObjectPair);
        domain_ = new JMLEqualsSet();
        imagePairSet_ = new JMLValueSet();
        size_ = 0;
    }

    /** Initialize this to be a relation containing a single association
     * between the given domain and range elements.
     * @see #singleton(Object, Object)
     * @see #JMLEqualsToObjectRelation(JMLEqualsObjectPair)
     */
    /*@  public normal_behavior
      @    requires dv != null && rv != null;
      @    assignable theRelation, owner, elementType, containsNull;
      @    ensures theRelation.int_size() == 1;
      @    ensures elementImage(dv).has(rv);
      @    ensures_redundantly isDefinedAt(dv);
      @*/
    public JMLEqualsToObjectRelation(/*@ non_null @*/ Object dv,
                                        /*@ non_null @*/ Object rv)
    {
        //@ set owner = null;
        //@ set containsNull = false;
        //@ set elementType = \type(JMLEqualsObjectPair);
        size_ = 1;
        domain_ = new JMLEqualsSet(dv);
        JMLObjectSet img = new JMLObjectSet(rv);
        imagePairSet_ = new JMLValueSet(new JMLEqualsValuePair(dv, img));
    }

    /** Initialize this to be a relation containing a single association
     *  given by the pair.
     * @see #singleton(JMLEqualsObjectPair)
     * @see #JMLEqualsToObjectRelation(Object, Object)
     */
    /*@  public normal_behavior
      @    requires pair != null;
      @    assignable theRelation, owner, elementType, containsNull;
      @    ensures theRelation.int_size() == 1 && theRelation.has(pair);
      @*/
    public JMLEqualsToObjectRelation(/*@ non_null @*/
                                        JMLEqualsObjectPair pair)
    {
        this(pair.key, pair.value);
    }

    /** Initialize this using the given representation.
     */
    /*@  protected normal_behavior
      @    requires ipset != null && dom != null && dom.int_size() <= sz;
      @    assignable theRelation, owner, elementType, containsNull;
      @    assignable_redundantly domain_, imagePairSet_, size_;
      @    ensures imagePairSet_ == ipset && domain_ == dom && size_ == sz;
      @
      @ implies_that
      @    requires ipset != null && dom != null && 0 <= sz;
      @    ensures imagePairSet_ == ipset && domain_ == dom && size_ == sz;
      @*/
    protected
        JMLEqualsToObjectRelation(/*@ non_null @*/ JMLValueSet ipset, 
                                     /*@ non_null @*/ JMLEqualsSet dom, 
                                     int sz)
    {
        //@ set owner = null;
        //@ set containsNull = false;
        //@ set elementType = \type(JMLEqualsObjectPair);
        domain_ = dom;
        imagePairSet_ = ipset;
        size_ = sz;
    }

    //**************************** Static methods ****************************

    /** The empty JMLEqualsToObjectRelation.
     * @see #JMLEqualsToObjectRelation()
     */
    public static final /*@ non_null @*/ JMLEqualsToObjectRelation EMPTY
        = new JMLEqualsToObjectRelation();

    /** Return the singleton relation containing the given association.
     * @see #singleton(JMLEqualsObjectPair)
     * @see #JMLEqualsToObjectRelation(Object, Object)
     */
    /*@ public normal_behavior
      @    requires dv != null && rv != null;
      @    ensures \result != null
      @         && \result.equals(new JMLEqualsToObjectRelation(dv, rv));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLEqualsToObjectRelation
        singleton(/*@ non_null @*/ Object dv,
                  /*@ non_null @*/ Object rv) {
        return new JMLEqualsToObjectRelation(dv, rv);
    }

    /** Return the singleton relation containing the association
     * described by the given pair.
     * @see #singleton(Object, Object)
     * @see #JMLEqualsToObjectRelation(JMLEqualsObjectPair)
     */
    /*@ public normal_behavior
      @    requires pair != null;
      @    ensures \result != null
      @         && \result.equals(singleton(pair.key, pair.value));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        JMLEqualsToObjectRelation
        singleton(/*@ non_null @*/ JMLEqualsObjectPair pair)
    {
        return singleton(pair.key, pair.value);
    }

    //**************************** Observers **********************************

    /** Tells whether this relation is a function.
     * @see JMLEqualsToObjectMap
     */
    /*@   public normal_behavior
      @     ensures \result == (\forall Object dv; isDefinedAt(dv);
      @                                  elementImage(dv).int_size() == 1);
      @*/
    public boolean isaFunction()
    {
        return size_ == domain_.int_size();
    }

    /** Returns a set containing all the range elements that this
     * relation relates to the given domain element.
     * @see #image
     * @see JMLEqualsToObjectMap#apply
     */
    /*@  public normal_behavior
      @    ensures (\forall JMLEqualsObjectPair pair;
      @                      theRelation.has(pair);
      @                      pair.keyEquals(dv) ==> \result.has(pair.value));
      @    ensures (\forall Object o; \result.has(o);
      @                  (\exists JMLEqualsObjectPair pair;
      @                      theRelation.has(pair);
      @                      pair.keyEquals(dv) && pair.valueEquals(o)));
      @    ensures_redundantly !isDefinedAt(dv) ==> \result.isEmpty();
      @
      @ implies_that
      @    ensures \result != null && !\result.containsNull;
      @*/
    public /*@ non_null @*/
        JMLObjectSet elementImage(/*@ nullable @*/ Object dv)
    {
        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            if (imagePair.keyEquals(dv)) {
                //@ assume imagePair.value != null;
                //@ assume imagePair.value instanceof JMLObjectSet;
                JMLObjectSet res = (JMLObjectSet) imagePair.value;
                //@ assume !res.containsNull;
                return res;
            }
        }
        return new JMLObjectSet();
    }

    /** Returns a set containing all the range elements that this
     * relation relates to the elements of the given set of domain elements.
     * @see #elementImage
     * @see #inverseImage
     * @see JMLEqualsToObjectMap#apply
     */
    /*@  public normal_behavior
      @    requires dom != null;
      @    ensures (\forall Object o; \result.has(o)
      @              <==> (\exists JMLEqualsObjectPair pair;
      @                      theRelation.has(pair);
      @                      dom.has(pair.key) && pair.valueEquals(o)));
      @    ensures_redundantly
      @              (\forall JMLEqualsObjectPair pair;
      @                      theRelation.has(pair);
      @                      dom.has(pair.key) ==> \result.has(pair.value));
      @
      @ implies_that
      @    ensures \result != null && !\result.containsNull;
      @*/
    public /*@ non_null @*/
        JMLObjectSet image(/*@ non_null @*/ JMLEqualsSet dom)
    {
        JMLObjectSet img = new JMLObjectSet();
        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        //@ loop_invariant !img.containsNull;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            if (dom.has(imagePair.key)) {
                JMLObjectSet ipv = (JMLObjectSet)imagePair.value;
                //@ assume !ipv.containsNull;
                img = img.union(ipv);
            }
        }
        return img;
    } //@ nowarn Exception;

    /** Returns the inverse of this relation.  The inverse is the
     *  relation that relates each range element to the corresponding
     *  domain element.
     * @see #inverseImage
     * @see #inverseElementImage
     */
    /*@  public normal_behavior
      @    ensures (\forall JMLObjectEqualsPair pair; ;
      @                 \result.theRelation.has(pair) 
      @                    == elementImage(pair.value).has(pair.key));
      @*/
    public /*@ non_null @*/ JMLObjectToEqualsRelation inverse()
    {
        JMLObjectToEqualsRelation invRel
            = new JMLObjectToEqualsRelation();
        JMLEqualsToObjectRelationEnumerator assocEnum = this.associations();
        JMLEqualsObjectPair pair;
        while (assocEnum.hasMoreElements()) {
            pair = assocEnum.nextPair();
            invRel = invRel.add(pair.value, pair.key);
        }
        return invRel;
    } //@ nowarn Exception;

    /** Return a set of all the domain elements that relate to the
     * given range element.
     * @see #inverseImage
     * @see #inverse
     * @see #elementImage
     */
    /*@  public normal_behavior
      @    ensures \result.equals(inverse().elementImage(rv));
      @
      @ implies_that
      @    ensures \result != null && !\result.containsNull;
      @*/
    public /*@ non_null @*/
        JMLEqualsSet inverseElementImage(Object rv)
    {
        JMLEqualsSet invImg = new JMLEqualsSet();
        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        //@ loop_invariant !invImg.containsNull;
        while (imagePairEnum.hasMoreElements()) { //@ nowarn LoopInv;
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null && imagePair.key != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            JMLObjectSet img = (JMLObjectSet) imagePair.value;
            if (img.has(rv)) {
                invImg = invImg.insert(imagePair.key);
            }
        }
        return invImg;
    } //@ nowarn Exception;

    /** Return a set of all the domain elements that relate to some
     * element in the given set of range elements.
     * @see #inverseElementImage
     * @see #inverse
     * @see #image
     */
    /*@  public normal_behavior
      @    requires rng != null;
      @    ensures \result.equals(inverse().image(rng));
      @
      @ implies_that
      @    ensures \result != null && !\result.containsNull;
      @*/
    public /*@ non_null @*/
        JMLEqualsSet inverseImage(/*@ non_null @*/ JMLObjectSet rng)
    {
        JMLEqualsSet invImg = new JMLEqualsSet();
        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        //@ loop_invariant !invImg.containsNull;
        while (imagePairEnum.hasMoreElements()) { //@ nowarn LoopInv;
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null && imagePair.key != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            JMLObjectSet img = (JMLObjectSet) imagePair.value;
            if (!img.intersection(rng).isEmpty()) {
                invImg = invImg.insert(imagePair.key);
            }
        }
        return invImg;
    } //@ nowarn Exception;

    /** Tells whether this relation associates any range element to the
     * given domain element.
     * @see #domain()
     */
    /*@  public normal_behavior
      @     ensures \result == (elementImage(dv).int_size() > 0);
      @     ensures_redundantly dv == null ==> !\result;
      @*/
    public boolean isDefinedAt(Object dv)
    {
        return domain_.has(dv);
    }

    /** Tells whether this associates the given key to the given value.
     * @see #isDefinedAt
     * @see #has(JMLEqualsObjectPair)
     */
    /*@  public normal_behavior
      @     ensures \result <==> domain().has(dv) && elementImage(dv).has(rv);
      @     ensures_redundantly dv == null || rv == null ==> !\result;
      @*/
    public /*@ pure @*/ boolean has(/*@ nullable @*/ Object dv, /*@ nullable @*/ Object rv)
    {
        //@ assume domain_.has(dv) ==> dv != null;
        return domain_.has(dv) && elementImage(dv).has(rv);
    }

    /** Tells whether this associates the given key to the given value.
     * @see #isDefinedAt
     * @see #has(Object, Object)
     */
    /*@  public normal_behavior
      @     requires pair != null;
      @     ensures \result <==> has(pair.key, pair.value);
      @*/
    public /*@ pure @*/ boolean has(/*@ non_null @*/ JMLEqualsObjectPair pair)
    {
        return has(pair.key, pair.value);
    }

    /** Tells whether this associates the given key to the given value.
     * @see #isDefinedAt
     * @see #has(JMLEqualsObjectPair)
     */
    /*@ also
      @    public normal_behavior
      @      ensures \result <==>
      @              obj != null
      @           && obj instanceof JMLEqualsObjectPair
      @           && has((JMLEqualsObjectPair) obj);
      @*/
    public /*@ pure @*/ boolean has(/*@ nullable @*/ Object obj)
    {
        return obj != null
                && obj instanceof JMLEqualsObjectPair
                && has((JMLEqualsObjectPair) obj);
    }

    /** Tells whether the relation is empty.
     * @see #int_size()
     */
    /*@  public normal_behavior
      @    ensures \result == (theRelation.int_size() == 0);
      @*/
    public boolean isEmpty()
    {
        return size_ == 0;
    }

    /** Return a clone of this object.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result instanceof JMLEqualsToObjectRelation
      @         && ((JMLEqualsToObjectRelation)\result)
      @                    .theRelation.equals(this.theRelation);
      @*/
    public Object clone()
    {
        return new
            JMLEqualsToObjectRelation(imagePairSet_, domain_, size_);
    } //@ nowarn Post;

    /** Test whether this object's value is equal to the given argument.
     */
    /*@ also
      @  public normal_behavior
      @    requires obj != null && obj instanceof JMLEqualsToObjectRelation;
      @    ensures \result == 
      @            this.theRelation.equals(
      @                    ((JMLEqualsToObjectRelation)obj).theRelation);
      @ also 
      @  public normal_behavior
      @    requires obj == null
      @          || !(obj instanceof JMLEqualsToObjectRelation);
      @    ensures !\result;
      @*/
    public boolean equals(/*@ nullable @*/ Object obj)
    {
        if (obj == null || !(obj instanceof JMLEqualsToObjectRelation)) {
            return false;
        }

        JMLEqualsToObjectRelation rel
            = (JMLEqualsToObjectRelation)obj;

        if (size_ != rel.int_size()) {
            return false;
        }

        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        JMLObjectSet img;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            img = (JMLObjectSet)imagePair.value;
            if (!img.equals(rel.elementImage(imagePair.key))) {
                return false;
            }
        }
        return true;
    }

    /** Return a hash code for this object.
     */
    public int hashCode() {
        return imagePairSet_.hashCode();
    }

    /** Returns a set containing the domain of this relation.
     * @see #domainElements()
     * @see #associations()
     * @see #isDefinedAt
     * @see #image
     * @see #range()
     * @see #inverse()
     */
    /*@  public normal_behavior
      @    ensures (\forall Object dv; ;
      @                 \result.has(dv) == isDefinedAt(dv));
      @*/
    public /*@ non_null @*/ JMLEqualsSet domain()
    {
        return domain_;
    }

    /** Returns a set containing the range of this relation.
     * @see #rangeElements()
     * @see #associations()
     * @see #inverseElementImage
     * @see #domain()
     * @see #inverse()
     */
    /*@  public normal_behavior
      @    ensures (\forall Object rv; ;
      @                 \result.has(rv) 
      @                    == (\exists Object dv; ;
      @                            elementImage(dv).has(rv)) 
      @                );
      @*/
    public /*@ non_null @*/ JMLObjectSet range()
    {
        JMLObjectSet rangeSet = new JMLObjectSet();

        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        JMLObjectSet img;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            img = (JMLObjectSet) imagePair.value;
            rangeSet = rangeSet.union(img);
        }
        return rangeSet;
    } //@ nowarn Exception;

    private static final String TOO_BIG_TO_INSERT
        = "Cannot insert into a Relation with Integer.MAX_VALUE elements.";

    /** Return a relation that is just like this relation, except that
     *  it also associates the given domain element to the given range
     *  element.
     * @see #insert
     */
    /*@  public normal_behavior
      @    requires dv != null && rv != null;
      @    requires int_size() < Integer.MAX_VALUE || elementImage(dv).has(rv);
      @    ensures \result.theRelation.equals(
      @           this.theRelation.insert(new JMLEqualsObjectPair(dv, rv)));
      @*/
    public /*@ pure @*/ /*@ non_null @*/ 
        JMLEqualsToObjectRelation add(/*@ non_null @*/ Object dv,
                                         /*@ non_null @*/ Object rv)
        throws NullPointerException, IllegalStateException
    {
        if (rv == null) {
            throw new NullPointerException();
        }

        JMLValueSet newImagePairSet;
        JMLEqualsSet newDom;
        int newSize;
        JMLObjectSet img;

        if (!domain_.has(dv)) {
            if (size_ == Integer.MAX_VALUE) {
                throw new IllegalStateException(TOO_BIG_TO_INSERT);
            }
            newDom = domain_.insert(dv);
            newSize = size_ + 1;
            img = new JMLObjectSet(rv);
            newImagePairSet
                = imagePairSet_.insert(new JMLEqualsValuePair(dv, img));
        } else {
            newImagePairSet = new JMLValueSet();
            newDom = domain_;
            newSize = 0;

            JMLEqualsToObjectRelationImageEnumerator imagePairEnum
                = this.imagePairs();
            JMLEqualsValuePair imagePair;
            while (imagePairEnum.hasMoreElements()) {
                imagePair = imagePairEnum.nextImagePair();
                //@ assume imagePair.value != null;
                //@ assume imagePair.value instanceof JMLObjectSet;
                img = (JMLObjectSet) imagePair.value;
                if (imagePair.keyEquals(dv)) {
                    img = img.insert(rv);
                }
                int size_inc = img.int_size();
                if (newSize <= Integer.MAX_VALUE - size_inc) {
                    newSize = newSize + size_inc;
                } else {
                    throw new IllegalStateException(TOO_BIG_TO_INSERT);
                }
                newImagePairSet 
                    = newImagePairSet
                    .insert(new JMLEqualsValuePair(imagePair.key, img));
            }
        }
        return new JMLEqualsToObjectRelation(newImagePairSet,
                                                newDom, newSize);
    }

    /** Return a relation that is just like this relation, except that
     *  it also includes the association described by the given pair.
     * @see #add
     */
    /*@  public normal_behavior
      @    requires pair != null;
      @    requires int_size() < Integer.MAX_VALUE
      @             || elementImage(pair.key).has(pair.value);
      @    ensures \result.theRelation.equals(this.theRelation.insert(pair));
      @*/
    public /*@ non_null @*/ 
        JMLEqualsToObjectRelation insert(/*@ non_null @*/
                                         JMLEqualsObjectPair pair)
        throws IllegalStateException
    {
        return add(pair.key, pair.value);
    } //@ nowarn Exception;

    /** Return a relation that is just like this relation, except that
     *  it does not contain any association with the given domain element.
     * @see #remove(JMLEqualsObjectPair)
     * @see #removeFromDomain
     */
    /*@  public normal_behavior
      @    ensures \result != null
      @         && (\forall Object val; domain().has(val);
      @             (\forall Object r; r != null;
      @                   (elementImage(val).has(r)
      @                      <==> \result.theRelation
      @                            .has(new JMLEqualsObjectPair(val,r))
      @                          && !val.equals(dv))));
      @ implies_that
      @   public normal_behavior
      @    requires dv == null;
      @    ensures \result != null && \result.equals(this);
      @*/
    public /*@ non_null @*/ 
        JMLEqualsToObjectRelation removeFromDomain(/*@ nullable @*/ Object dv)
    {
        if (!domain_.has(dv)) {
            return(this);
        }

        JMLValueSet newImagePairSet = new JMLValueSet();
        JMLEqualsSet newDom = domain_.remove(dv);
        int newSize = 0;

        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            if (!imagePair.keyEquals(dv)) {
                newImagePairSet = newImagePairSet.insert(imagePair);
                JMLObjectSet img = (JMLObjectSet) imagePair.value;
                newSize = newSize + img.int_size();
            }
        }
        return new JMLEqualsToObjectRelation(newImagePairSet,
                                                newDom, newSize);
    } //@ nowarn Exception;

    /** Return a relation that is just like this relation, except that
     *  it does not contain the association, if any, between the given
     *  domain and range elements.
     * @see #removeFromDomain
     * @see #remove(Object, Object)
     * @see #remove(JMLEqualsObjectPair)
     */
    /*@  public normal_behavior
      @    requires dv != null && rv != null;
      @    ensures \result.theRelation.equals(
      @                theRelation.remove(new JMLEqualsObjectPair(dv, rv)));
      @   also
      @    requires dv == null || rv == null;
      @    ensures \result != null && \result.equals(this);
      @*/
    public /*@ non_null @*/ 
        JMLEqualsToObjectRelation remove(Object dv, Object rv)
    {
        if (!domain_.has(dv)) {
            return(this);
        }
        //@ assume dv != null;

        JMLValueSet newImagePairSet = new JMLValueSet();
        JMLEqualsSet newDom = domain_;
        int newSize = 0;

        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        JMLObjectSet img;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            img = (JMLObjectSet) imagePair.value;
            int imgSize = img.int_size();
            if (imagePair.keyEquals(dv)) {
                img = img.remove(rv);
                imgSize = img.int_size();
                if (imgSize > 0) {
                    newImagePairSet
                        = newImagePairSet
                        .insert(new JMLEqualsValuePair(dv, img));
                    newSize = newSize + imgSize;
                } else {
                    //@ assert imgSize == 0;
                    newDom = newDom.remove(dv);
                }
            } else {
                newImagePairSet = newImagePairSet.insert(imagePair);
                newSize = newSize + imgSize;
            }
        }
        return new JMLEqualsToObjectRelation(newImagePairSet,
                                                newDom, newSize);
    } //@ nowarn Exception;


    /** Return a relation that is just like this relation, except that
     *  it does not contain association described by the given pair.
     * @see #remove(Object, Object)
     * @see #removeFromDomain
     */
    /*@  public normal_behavior
      @    requires pair != null;
      @    ensures \result.theRelation.equals(this.theRelation.remove(pair));
      @*/
    public /*@ non_null @*/ 
        JMLEqualsToObjectRelation remove(/*@ non_null @*/
                                            JMLEqualsObjectPair pair)
    {
        return remove(pair.key, pair.value);
    }

    /** Return a relation that is the composition of the given
     *  relation and this relation.  The composition is done in the
     *  "usual" order, so that if the given relation relates x to y,
     *  and this relation relates y to z, then the result relates x to
     *  z.
     *  @see #compose(JMLObjectToEqualsRelation)
     */
    /*@  public normal_behavior
      @    requires othRel != null;
      @    ensures (\forall JMLValueObjectPair pair; ;
      @                 \result.theRelation.has(pair) 
      @                    == (\exists Object val;
      @                            othRel.elementImage(pair.key).has(val);
      @                            this.elementImage(val).has(pair.value)
      @                            )
      @                );
      @*/
    public /*@ non_null @*/ 
        JMLValueToObjectRelation
        compose(/*@ non_null @*/ JMLValueToEqualsRelation othRel)
    {
        JMLValueSet newImagePairSet = new JMLValueSet();
        JMLValueSet newDom = new JMLValueSet();
        int newSize = 0;

        JMLValueToEqualsRelationImageEnumerator imagePairEnum
            = othRel.imagePairs();
        JMLValueValuePair imagePair;
        JMLEqualsSet img1;
        JMLObjectSet img2;
        int imgSize;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLEqualsSet;
            img1 = (JMLEqualsSet)imagePair.value;
            img2 = this.image(img1);
            imgSize = img2.int_size();
            if (imgSize > 0) {
                newImagePairSet
                    = newImagePairSet
                    .insert(new JMLValueValuePair(imagePair.key, img2));
                newSize = newSize + imgSize;
                newDom = newDom.insert(imagePair.key);
            }
        }
        return new JMLValueToObjectRelation(newImagePairSet, newDom, newSize);
    } //@ nowarn Exception;

    /** Return a relation that is the composition of the given
     *  relation and this relation.  The composition is done in the
     *  "usual" order, so that if the given relation relates x to y,
     *  and this relation relates y to z, then the result relates x to
     *  z.
     *  @see #compose(JMLValueToEqualsRelation)
     */
    /*@  public normal_behavior
      @    requires othRel != null;
      @    ensures (\forall JMLValueObjectPair pair; ;
      @                 \result.theRelation.has(pair) 
      @                    == (\exists Object val;
      @                            othRel.elementImage(pair.key).has(val);
      @                            this.elementImage(val).has(pair.value)
      @                            )
      @                );
      @*/
    public /*@ non_null @*/ 
        JMLObjectToObjectRelation
        compose(/*@ non_null @*/ JMLObjectToEqualsRelation othRel)
    {
        JMLValueSet newImagePairSet = new JMLValueSet();
        JMLObjectSet newDom = new JMLObjectSet();
        int newSize = 0;

        JMLObjectToEqualsRelationImageEnumerator imagePairEnum
            = othRel.imagePairs();
        JMLObjectValuePair imagePair;
        JMLEqualsSet img1;
        JMLObjectSet img2;
        int imgSize;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLEqualsSet;
            img1 = (JMLEqualsSet) imagePair.value;
            img2 = this.image(img1);
            imgSize = img2.int_size();
            if (imgSize > 0) {
                newImagePairSet
                    = newImagePairSet
                    .insert(new JMLObjectValuePair(imagePair.key, img2));
                newSize = newSize + imgSize;
                newDom = newDom.insert(imagePair.key);
            }
        }
        return new JMLObjectToObjectRelation(newImagePairSet, newDom,
                                              newSize);
    } //@ nowarn Exception;

    /** Return a relation that union of the this and the given relation.
     *  This is the union of the sets of associations.
     *  @see #difference
     *  @see #intersection
     */
    /*@  public normal_behavior
      @    requires othRel != null;
      @    requires int_size()
      @             < Integer.MAX_VALUE - othRel.difference(this).int_size();
      @    ensures \result.theRelation.equals(
      @                    this.theRelation.union(othRel.theRelation));
      @*/
    public /*@ non_null @*/ 
        JMLEqualsToObjectRelation 
        union(/*@ non_null @*/ JMLEqualsToObjectRelation othRel)
        throws IllegalStateException
    {
        JMLValueSet newImagePairSet = new JMLValueSet();
        JMLEqualsSet newDom = domain_;
        int newSize = 0;

        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        JMLObjectSet img;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            img = (JMLObjectSet) imagePair.value;
            img = img.union(othRel.elementImage(imagePair.key));
            newImagePairSet
                = newImagePairSet
                .insert(new JMLEqualsValuePair(imagePair.key, img));
            int size_inc = img.int_size();
            if (newSize <= Integer.MAX_VALUE - size_inc) {
                newSize = newSize + size_inc;
            } else {
                throw new IllegalStateException(TOO_BIG_TO_UNION);
            }
        }
        JMLEqualsSet diffDom = othRel.domain().difference(this.domain_);
        imagePairEnum = othRel.imagePairs();
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            if (diffDom.has(imagePair.key)) {
                newImagePairSet = newImagePairSet.insert(imagePair);
                newDom = newDom.insert(imagePair.key);
                //@ assume imagePair.value != null;
                //@ assume imagePair.value instanceof JMLObjectSet;
                img = (JMLObjectSet) imagePair.value;
                int size_inc = img.int_size();
                if (newSize <= Integer.MAX_VALUE - size_inc) {
                    newSize = newSize + size_inc;
                } else {
                    throw new IllegalStateException(TOO_BIG_TO_UNION);
                }
            }
        }
        return new JMLEqualsToObjectRelation(newImagePairSet, newDom,
                                                newSize);
    }

    protected static final String TOO_BIG_TO_UNION
        = "Cannot make a union with more than Integer.MAX_VALUE elements.";

    /** Return a relation that is the intersection of this and the
     *  given relation.  This is the intersection of the sets of
     *  associations.
     *  @see #difference
     *  @see #union
     */
    /*@  public normal_behavior
      @    requires othRel != null;
      @    ensures \result.theRelation.equals(
      @                    this.theRelation.intersection(othRel.theRelation));
      @*/
    public /*@ non_null @*/ 
        JMLEqualsToObjectRelation
        intersection(/*@ non_null @*/ JMLEqualsToObjectRelation othRel)
    {
        JMLValueSet newImagePairSet = new JMLValueSet();
        JMLEqualsSet newDom = new JMLEqualsSet();
        int newSize = 0;

        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        JMLObjectSet img;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            img = (JMLObjectSet) imagePair.value;
            img = img.intersection(othRel.elementImage(imagePair.key));
            if (!img.isEmpty()) {
                newImagePairSet
                    = newImagePairSet
                    .insert(new JMLEqualsValuePair(imagePair.key, img));
                newDom = newDom.insert(imagePair.key);
                newSize = newSize + img.int_size();
            }
        }
        return new JMLEqualsToObjectRelation(newImagePairSet, newDom,
                                                newSize);
    } //@ nowarn Exception;

    /** Return a relation that is the difference between this and the given
     * relation.  This is the difference between the sets of
     * associations.
     *  @see #difference
     *  @see #intersection
     */
    /*@  public normal_behavior
      @    requires othRel != null;
      @    ensures \result.theRelation.equals(
      @                    this.theRelation.difference(othRel.theRelation));
      @*/
    public /*@ non_null @*/  
        JMLEqualsToObjectRelation
        difference(/*@ non_null @*/ JMLEqualsToObjectRelation othRel)
    {
        JMLValueSet newImagePairSet = new JMLValueSet();
        JMLEqualsSet newDom = new JMLEqualsSet();
        int newSize = 0;

        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        JMLObjectSet img;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            img = (JMLObjectSet) imagePair.value;
            img = img.difference(othRel.elementImage(imagePair.key));
            if (!img.isEmpty()) {
                newImagePairSet
                    = newImagePairSet
                    .insert(new JMLEqualsValuePair(imagePair.key, img));
                newDom = newDom.insert(imagePair.key);
                newSize = newSize + img.int_size();
            }
        }
        return new JMLEqualsToObjectRelation(newImagePairSet, newDom,
                                                newSize);
    } //@ nowarn Exception;

    /** Return a relation that is like this relation except that its
     * domain is limited to just the elements of the given set.
     *  @see #restrictRangeTo
     */
    /*@  public normal_behavior
      @    requires dom != null;
      @    ensures (\forall JMLEqualsObjectPair pair; pair != null;
      @                      \result.theRelation.has(pair) == dom.has(pair.key)
      @                    && elementImage(pair.key).has(pair.value)
      @                );
      @*/
    public /*@ non_null @*/ 
        JMLEqualsToObjectRelation 
        restrictDomainTo(/*@ non_null @*/ JMLEqualsSet dom)
    {
        JMLValueSet newImagePairSet = new JMLValueSet();
        JMLEqualsSet newDom = domain_.intersection(dom);
        //@ assume (\forall Object dv; newDom.has(dv); dv != null);
        int newSize = 0;

        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        JMLObjectSet img;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            if (newDom.has(imagePair.key)) {
                newImagePairSet = newImagePairSet.insert(imagePair);
                img = (JMLObjectSet) imagePair.value;
                newSize = newSize + img.int_size();
            }
        }
        return new JMLEqualsToObjectRelation(newImagePairSet, newDom,
                                                newSize);
    } //@ nowarn Exception;

    /** Return a relation that is like this relation except that its
     * range is limited to just the elements of the given set.
     *  @see #restrictDomainTo
     */
    /*@  public normal_behavior
      @    requires rng != null;
      @    ensures (\forall JMLEqualsObjectPair pair; ;
      @                       \result.theRelation.has(pair)
      @                        == rng.has(pair.value) 
      @                    && elementImage(pair.key).has(pair.value)
      @                );
      @*/
    public /*@ non_null @*/ 
        JMLEqualsToObjectRelation
        restrictRangeTo(/*@ non_null @*/ JMLObjectSet rng)
    {
        JMLValueSet newImagePairSet = new JMLValueSet();
        JMLEqualsSet newDom = new JMLEqualsSet();
        int newSize = 0;

        JMLEqualsToObjectRelationImageEnumerator imagePairEnum
            = this.imagePairs();
        JMLEqualsValuePair imagePair;
        JMLObjectSet img;
        while (imagePairEnum.hasMoreElements()) {
            imagePair = imagePairEnum.nextImagePair();
            //@ assume imagePair.value != null;
            //@ assume imagePair.value instanceof JMLObjectSet;
            img = ((JMLObjectSet)imagePair.value).intersection(rng);
            if (!img.isEmpty()) {
                newImagePairSet
                    = newImagePairSet
                    .insert(new JMLEqualsValuePair(imagePair.key, img));
                newDom = newDom.insert(imagePair.key);
                newSize = newSize + img.int_size();
            }
        }
        return new JMLEqualsToObjectRelation(newImagePairSet, newDom,
                                                newSize);
    } //@ nowarn Exception;

    /** Return a string representation of this object.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result.equals(theRelation.toString());
      @*/
    public String toString()
    {
        return toSet().toString();
    }

    /** Return a enumerator for the set of associations that
     * conceptually make up this relation.
     *  @see #elements()
     *  @see #iterator()
     *  @see #toSet()
     *  @see #imagePairs()
     */
    /*@  public normal_behavior
      @    ensures \result != null &&
      @      \result.equals(new JMLEqualsToObjectRelationEnumerator(this));
      @*/
    public /*@ non_null @*/
        JMLEqualsToObjectRelationEnumerator associations()
    {
        return new JMLEqualsToObjectRelationEnumerator(this);
    }

    /** Return a enumerator for the set of associations that
     * conceptually make up this relation.  This is a synonym for associations.
     *  @see #associations()
     *  @see #iterator()
     */
    /*@  public normal_behavior
      @    ensures \result != null &&
      @      \result.equals(associations());
      @*/
    public /*@ non_null @*/
        JMLEqualsToObjectRelationEnumerator elements()
    {
        return associations();
    }

    /** Returns an Iterator over the set of pairs conceptually
     *  contained in this relation..
     *  @see #associations()
     *  @see #elements()
     */
    /*@ also
      @    public normal_behavior
      @      ensures \fresh(\result)
      @          && \result.equals(new JMLEnumerationToIterator(elements()));
      @*/  
    public JMLIterator iterator() {
        return new JMLEnumerationToIterator(elements());
    }  //@ nowarn Post;

    /** Return the set of all associations in this relation.
     *  @see #associations()
     *  @see #toBag()
     *  @see #toSequence()
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.size == int_size()
      @        && (\forall JMLType pv; \result.has(pv);
      @                pv != null && pv instanceof JMLEqualsObjectPair
      @             && this.isDefinedAt(((JMLEqualsObjectPair)pv).key)
      @             && this.elementImage(((JMLEqualsObjectPair)pv).key)
      @                    .has(((JMLEqualsObjectPair)pv).value));
      @             
      @*/
    public /*@ non_null @*/ JMLValueSet toSet() {
        JMLEqualsToObjectRelationEnumerator pairEnum = this.associations();
        JMLValueSet ret = new JMLValueSet();
        while (pairEnum.hasMoreElements()) {
            //@ assume pairEnum.moreElements;
            JMLEqualsObjectPair p = pairEnum.nextPair();
            ret = ret.insert(p);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return the bag of all associations in this relation.
     *  @see #toSet()
     *  @see #toSequence()
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.equals(toSet().toBag());
      @*/
    public /*@ non_null @*/ JMLValueBag toBag() {
        JMLEqualsToObjectRelationEnumerator pairEnum = this.associations();
        JMLValueBag ret = new JMLValueBag();
        while (pairEnum.hasMoreElements()) {
            //@ assume pairEnum.moreElements;
            JMLEqualsObjectPair p = pairEnum.nextPair();
            ret = ret.insert(p);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return a sequence containing all associations in this relation.
     *  @see #toSet()
     *  @see #toBag()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall JMLEqualsObjectPair p;; 
      @                         \result.count(p) == 1 <==> this.has(p));
      @*/
    public /*@ non_null @*/ JMLValueSequence toSequence() {
        JMLEqualsToObjectRelationEnumerator pairEnum = this.associations();
        JMLValueSequence ret = new JMLValueSequence();
        while (pairEnum.hasMoreElements()) {
            //@ assume pairEnum.moreElements;
            JMLEqualsObjectPair p = pairEnum.nextPair();
            ret = ret.insertFront(p);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return the set of image set pairs that make up this relation.
     *  @see #imagePairs()
     *  @see #toSet()
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.int_size() == domain().int_size()
      @        && (\forall Object dv; domain().has(dv);
      @                \result.has(
      @                    new JMLEqualsValuePair(dv, elementImage(dv))));
      @*/
    public /*@ non_null @*/ JMLValueSet imagePairSet() {
        return imagePairSet_;
    }

    /** Return the set of domain image set pairs that make up this relation.
     *  @see #imagePairSet()
     *  @see #associations()
     *  @see #toSet()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @        && \result.abstractValue().int_size() == domain().int_size()
      @        && (\forall Object dv; domain().has(dv);
      @                \result.abstractValue().has(
      @                    new JMLEqualsValuePair(dv, elementImage(dv))));
      @*/
    public /*@ non_null @*/
        JMLEqualsToObjectRelationImageEnumerator imagePairs() {
        return new JMLEqualsToObjectRelationImageEnumerator(this);
    }


    /** Return a enumerator for the set that is the domain of this
     * relation.
     * @see #domain()
     * @see #rangeElements()
     */
    /*@  public normal_behavior
      @    ensures \result.equals(domain().elements());
      @*/
    public /*@ non_null @*/ JMLEqualsSetEnumerator domainElements()
    {
        return domain_.elements();
    }

    /** Return a enumerator for the set that is the range of this
     * relation.  (This was formerly called "elements").
     * @see #range()
     * @see #domainElements()
     */
    /*@  public normal_behavior
      @    ensures \result.equals(range().elements());
      @*/
    public /*@ non_null @*/ JMLObjectSetEnumerator rangeElements()
    {
        return range().elements();
    }

    /** Return the number of associations in this relation.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result == theRelation.int_size();
      @*/
    public int int_size()
    {
        return size_;
    }

    /** Return a map that is contained in this relation.  If this
     * relation is a function, then this method can be seen as a type
     * conversion which does not make a change to the abstract value.
     * However, if this relation is not a function, then this method
     * chooses a function contained in this relation from among the
     * possibilities available.
     * @see #isaFunction
     * @see JMLEqualsToObjectMap
     */
    /*@  public normal_behavior
      @    ensures (\forall Object dv; dv != null;
      @             (this.isDefinedAt(dv) == \result.isDefinedAt(dv))
      @             && \result.elementImage(dv).isSubset(this.elementImage(dv))
      @             && \result.elementImage(dv).int_size() == 1);
      @*/
    public /*@ non_null @*/ JMLEqualsToObjectMap toFunction()
    {
        JMLEqualsSet newDom = domain_;
        int newSize = domain_.int_size();

        JMLValueSet newImagePairSet = imagePairSet_;

        if (newSize != size_) {
            // Have to restrict the result to be a function
            JMLEqualsToObjectRelationImageEnumerator imagePairEnum
                = this.imagePairs();
            newImagePairSet = new JMLValueSet();
            JMLEqualsValuePair imagePair;
            JMLObjectSet img;
            while (imagePairEnum.hasMoreElements()) {
                imagePair = imagePairEnum.nextImagePair();
                //@ assume imagePair.value != null;
                //@ assume imagePair.value instanceof JMLObjectSet;
                img = (JMLObjectSet) imagePair.value;
                Enumeration imgEnum = img.elements();
                //@ assume imgEnum.moreElements;
                Object o = imgEnum.nextElement();
                if (o == null) {
                    img = new JMLObjectSet(null);
                } else {
                    //@ assume o != null && o instanceof Object;
                    Object rv = (Object) o;
                    img = new JMLObjectSet(rv);
                }
                newImagePairSet
                    = newImagePairSet
                    .insert(new JMLEqualsValuePair(imagePair.key, img));
            }
        }
        return new JMLEqualsToObjectMap(newImagePairSet, newDom, newSize);
    } //@ nowarn Exception;
}
