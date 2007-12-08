// @(#)$Id: SortedMap.spec,v 1.11 2006/01/24 17:09:48 leavens Exp $

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

import java.io.*;
//@ model import org.jmlspecs.models.*;

/** JML's specification of java.util.SortedMap.
 * @version $Revision: 1.11 $
 * @author Katie Becker
 */
public interface SortedMap extends Map {

    //@ public model instance JMLType firstKey;  
    //+@     in theMap;
    //@ public model instance JMLType lastKey;
    //+@        in theMap;
    
    /*@ public normal_behavior
      @    ensures true;
      @*/  
    /*@ pure @*/ Comparator comparator(); 

    /*@ public behavior
      @    assignable \nothing;
      @    ensures (\result.firstKey.equals(firstKey));
      @    ensures \result != null;
      @    signals_only ClassCastException, IllegalArgumentException,
      @                 NullPointerException;
      @    signals (ClassCastException)
      @            (* \typeof(fromKey) or \typeof(toKey)
      @             is incompatible with this map's comparator *); 
      @    signals (IllegalArgumentException) 
      @            (* fromKey > toKey || fromKey or toKey is not
      @             within the domain of the SortedMap *); 
      @    signals (NullPointerException) 
      @            (fromKey==null || toKey==null) && !containsNull;
      @*/
    /*@ pure @*/ SortedMap subMap(Object fromKey, Object toKey); 
  
            
    /*@ public behavior
      @    assignable \nothing;
      @    ensures (\result.firstKey.equals(firstKey));
      @    ensures \result != null;
      @    signals_only ClassCastException, IllegalArgumentException,
      @                 NullPointerException;
      @    signals (ClassCastException)
      @            (* \typeof(toKey) is incompatible with
      @             with this map's comparator *); 
      @    signals (IllegalArgumentException) 
      @            (* toKey is not within the domain of the
      @             SortedMap *); 
      @    signals (NullPointerException) toKey==null 
      @             && !containsNull;
      @*/  
    /*@ pure @*/ SortedMap headMap(Object toKey); 

    /*@ public behavior
      @    assignable \nothing;
      @    ensures \result != null;
      @    signals_only ClassCastException, IllegalArgumentException,
      @                 NullPointerException;
      @    signals (ClassCastException)
      @            (* \typeof(fromKey) is incompatible with this
      @             map's comparator *); 
      @    signals (IllegalArgumentException) 
      @            (* fromKey is not within the domain of the 
      @             SortedMap *); 
      @    signals (NullPointerException) fromKey==null 
      @             && !containsNull;
      @*/          
    /*@ pure @*/ SortedMap tailMap(Object fromKey); 

    /*@ public behavior
      @    assignable \nothing;
      @    ensures \result.equals(firstKey);
      @    signals_only NoSuchElementException;
      @    signals (NoSuchElementException) isEmpty();
      @*/
    /*@ pure @*/ Object firstKey(); 

    /*@ public behavior
      @    assignable \nothing;
      @    ensures \result.equals(lastKey);
      @    signals_only NoSuchElementException;
      @    signals (NoSuchElementException) isEmpty();
      @*/
    /*@ pure @*/ Object lastKey(); 

}
