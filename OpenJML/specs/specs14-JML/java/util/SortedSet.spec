// @(#)$Id: SortedSet.spec,v 1.9 2006/01/24 17:09:48 leavens Exp $

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

/** JML's specification of java.util.SortedSet.
 * @version $Revision: 1.9 $
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public /*@ pure @*/ interface SortedSet extends Set {

    //@ public model instance JMLType firstElement;
    //@ public model instance JMLType lastElement;
    
    /*@ public normal_behavior
      @    ensures true;
      @*/  
    /*@ pure @*/ Comparator comparator();

    /*@ public behavior
      @    ensures \result != null;
      @ //!FIXME! add in the following when can do JMLEqualsSet comprehensions
      @ //        && \result.theSet.equals(
      @ //                new JMLEqualsSet{ Object o | this.has(o) && o != null
      @ //                     && 0 <= comparator().compare(fromElement, o)
      @ //                     && comparator().compare(o, toElement) > 0});
      @    signals_only ClassCastException, IllegalArgumentException,
      @                 NullPointerException;
      @    signals (ClassCastException)
      @           (* \typeof(fromElement) or \typeof(toElement)
      @            is incompatible with this set's comparator *); 
      @    signals (IllegalArgumentException) 
      @           (* fromElement > toElement || fromElement or 
      @            toElement is not within the domain of 
      @            the SortedSet *); 
      @    signals (NullPointerException) 
      @            (fromElement==null || toElement==null) 
      @             && !containsNull;
      @*/
    SortedSet subSet(Object fromElement, Object toElement); 

    /*@ public behavior
      @    ensures (\result.firstElement.equals(firstElement));
      @    ensures \result != null;
      @    signals_only ClassCastException, IllegalArgumentException,
      @                 NullPointerException;
      @    signals (ClassCastException)
      @            (* \typeof(toElement) is incompatible with
      @             with this set's comparator *); 
      @    signals (IllegalArgumentException) 
      @            (* toElement is not within the domain of 
      @             the SortedSet *); 
      @    signals (NullPointerException) toElement==null && !containsNull;
      @*/
    SortedSet headSet(Object toElement); 
    
    /*@ public behavior
      @    ensures \result != null;
      @ //!FIXME! specify more of the behavior
      @    signals_only ClassCastException, IllegalArgumentException,
      @                 NullPointerException;
      @    signals (ClassCastException)
      @           (* \typeof(fromElement) is incompatible with this
      @            set's comparator *); 
      @    signals (IllegalArgumentException) 
      @           (* fromKey is not within the domain of 
      @            the SortedSet *); 
      @    signals (NullPointerException) fromElement==null 
      @             && !containsNull;
      @*/ 
    SortedSet tailSet(Object fromElement); 

    /*@ public behavior
      @    ensures \result.equals(firstElement);
      @    signals_only NoSuchElementException;
      @    signals (NoSuchElementException) theSet.isEmpty();
      @*/
    Object first(); 
   
    /*@ public behavior
      @    ensures \result.equals(lastElement);
      @    signals_only NoSuchElementException;
      @    signals (NoSuchElementException) theSet.isEmpty();
      @*/
    Object last(); 

}
