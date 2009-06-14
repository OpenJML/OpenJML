// @(#)$Id: CharSequence.spec 2022 2006-08-13 02:36:42Z chalin $

// Copyright (C) 2002 Iowa State University

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

/** JML's specification of java.lang.CharSequence.
 * @version $Revision: 2022 $
 * @author Gary T. Leavens
 * @author David Cok
 */
public interface CharSequence {
    //@ public instance model non_null char[] charArray;
    //@ public invariant charArray.owner == this;

    /*@ public normal_behavior
      @   ensures \result <==> ( charArray != null && charArray.owner == this);
      @ public pure model boolean initialCharSequence();
      @*/

    /*@ public normal_behavior
        ensures \result == ( a == b || (a != null && b != null &&
                      a.length == b.length && 
                      equal(a,0,b,0,a.length) ));
        public static pure model boolean equal(char[] a, char[] b);
     */
    /*@ public normal_behavior
        requires a != null && b!= null && astart >= 0 && bstart >= 0 &&
                 length >= 0 &&
                 astart+length <= a.length && bstart + length <= b.length;
        ensures \result == ((a==b && astart == bstart) ||
                      (\forall int i; 0<=i && i<length; a[i+astart] == b[i+bstart])); 
        public static pure model boolean equal(char[] a, int astart, char[] b, int bstart, int length);
     */

    //@ axiom (\forall char[] a;; equal(a,a));
    //@ axiom (\forall char[] a,b;; equal(a,b) <==> equal(b,a));
    //@ axiom (\forall char[] a,b,c;; (equal(a,b) && equal(b,c))==>equal(a,c)); 

    //@ public normal_behavior
    //@      ensures \result >= 0;
    //@      ensures \result == charArray.length;
    //@ pure
    int length();

    /*@   public normal_behavior
      @      requires 0 <= index && index < charArray.length;
      @      ensures  \result == charArray[index];
      @  also
      @    public exceptional_behavior
      @      requires !(0 <= index && index < charArray.length);
      @      signals_only IndexOutOfBoundsException;
      @*/
    //@ pure
    char charAt(int index) throws IndexOutOfBoundsException;

    /*@   public normal_behavior
      @      requires 0 <= start && start <= end && end <= charArray.length;
      @      ensures \result != null;
      @      ensures \result.charArray.length == end-start;
      @      ensures equal(\result.charArray,0,charArray,start,end-start);
      @      ensures start==0 && end == length() ==>
      @                          equal(\result.charArray, this.charArray);
      @  also
      @    public exceptional_behavior
      @      requires start < 0 || end < start || end > charArray.length;
      @      signals_only IndexOutOfBoundsException;
      @*/
    //@ pure
    CharSequence subSequence(int start, int end)
        throws IndexOutOfBoundsException;

    /*@ also
      @    public normal_behavior
      @   assignable \not_specified;
      @      ensures \result != null
      @           && equal(\result.charArray,charArray);
      @*/
    public String toString();

    /** According to the javadocs, the equals method should not be called. */
    public boolean equals(Object obj);

    /** According to the javadocs, the hashCode method should not be called. */
    public int hashCode();
}
