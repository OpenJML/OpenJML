// Copyright (C) 2003 Iowa State University

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
// along with GNU Emacs; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.util;

import java.io.*;

/** JML's specification of java.util.HashMap.
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public class HashMap extends AbstractMap
    implements Map, Cloneable, Serializable
{
    /*@ public normal_behavior
      @   ensures \result <==> ( initialAbstractMap() &&
                                 initialCapacity >= i &&
                                 loadFactor == f);
      @ public pure model boolean initialHashMap(int i, double f);
      @
      @ public normal_behavior
      @   ensures \result <==> initialHashMap(16,0.75);
      @ public pure model boolean initialHashMap();
      @*/

    //@ public model int initialCapacity;    
    final /*@ spec_public @*/ float loadFactor;
    
    //@ public invariant initialCapacity >= 0;  
    //@ public invariant loadFactor > 0;
    
     /*@ public normal_behavior
       @    requires initialCapacity >= 0;
       @    ensures initialHashMap(initialCapacity,loadFactor);
       @*/ 
    //@ pure
    public HashMap(int initialCapacity, float loadFactor);

    /*@ public normal_behavior
       @    requires initialCapacity >= 0;
       @    ensures initialHashMap(initialCapacity,0.75);
       @*/
    //@ pure
    public HashMap(int initialCapacity);

    /*@ public normal_behavior
       @   ensures initialHashMap();
       @*/
    //@ pure
    public HashMap();

     /*@ public behavior
       @    requires m != null;
       @    ensures initialAbstractMap();
       @    ensures loadFactor == 0.75 
       @         && equals(m);
       @    ensures initialCapacity >= m.size();
            // FIXME - exceptions might get thrown if entries cannot be added
       @ also public exceptional_behavior
       @    requires m == null;
       @    assignable \nothing;
       @    signals_only NullPointerException;
       @*/
    //@ pure
    public HashMap(Map m);

    // specified by Map
    public int size();

    // specified by Map
    public boolean isEmpty();

    // specified by Map   
    public Object get(Object key);

    // specified by Map
    public boolean containsKey(Object key); 

    // specified by Map     
    public Object put(Object key, Object value); 

    // specified by Map     
    public void putAll(Map t); 

    // specified by Map     
    public Object remove(Object key);

    // specified by Map
    public void clear();

    // specified by Map 
    public boolean containsValue(Object value); 

    /*@ also
       @   public normal_behavior
       @     assignable \nothing;
       @     ensures \result instanceof Map && \fresh(\result)
       @          && ((Map)\result).equals(this);
       @     ensures_redundantly \result != this;
       @*/    
    public Object clone();

    // specified by Map      
    public Set keySet(); 

    // specified by Map     
    public Collection values(); 
 
    // specified by Map
    public Set entrySet(); 

}
