// @(#)$Id: CharSequence.spec,v 1.14 2005/12/23 17:02:04 chalin Exp $

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

package java.lang;

/** JML's specification of java.lang.CharSequence.
 * @version $Revision: 1.14 $
 * @author Gary T. Leavens
 */
public interface CharSequence {
    //@ public instance model char[] charArray;
    //@ public invariant charArray != null;
    //@ public invariant charArray.owner == this;

    /*@ public normal_behavior
        ensures \result == ( a == b || (a != null && b != null &&
                      a.length == b.length && 
                      (\forall int i; 0<=i && i<a.length; a[i] == b[i]))); 
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
    //@      modifies objectState;
    //@      ensures \result >= 0;
    //@      ensures \result == charArray.length;
    int length();

    /*@   public normal_behavior
      @      requires 0 <= index && index < charArray.length;
      @      modifies objectState;
      @      ensures  \result == charArray[index];
      @  also
      @    public exceptional_behavior
      @      requires !(0 <= index && index < charArray.length);
      @      modifies objectState;
      @      signals_only IndexOutOfBoundsException;
      @*/
    char charAt(int index) throws IndexOutOfBoundsException;

    /*@   public normal_behavior
      @      requires 0 <= start && start <= end && end <= charArray.length;
      @      modifies objectState;
      @      ensures \result.charArray.length == end-start;
      @      ensures equal(\result.charArray,0,charArray,start,end-start);
      @  also
      @    public exceptional_behavior
      @      requires start < 0 || end < start || end > charArray.length;
      @      modifies objectState;
      @      signals_only IndexOutOfBoundsException;
      @*/
    CharSequence subSequence(int start, int end)
        throws IndexOutOfBoundsException;

    /*@ also
      @    public normal_behavior
      @      modifies objectState;
      @      ensures \result != null
      @           && equal(\result.charArray,charArray);
      @*/
    public /*@ non_null @*/ String toString();

    /** According to the javadocs, the equals method should not be called. */
    //@ also
    //@      requires false;
    // @      modifies objectState;
    public boolean equals(/*@ nullable @*/ Object obj);

    /** According to the javadocs, the hashCode method should not be called. */
    //@ also
    //@    requires false;
    //@      modifies objectState;
    public int hashCode();
}
