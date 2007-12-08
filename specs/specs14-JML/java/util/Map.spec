// @(#)$Id: Map.spec,v 1.19 2006/01/30 22:10:45 leavens Exp $

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

//@ import org.jmlspecs.models.*;

/** JML's specification of java.util.Map.
 * @version $Revision: 1.19 $
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public interface Map {
    // Map uses equals.  For some reason the ESC/Java folks don't like
    // using JMLNullSafe.equals, but the code below doesn't have a method body,
    // so it isn't useful in runtime checking
    /*@ public normal_behavior
      @   ensures \result == ( o == oo ||
      @        ( o != null && oo != null && o.equals(oo)));
      @ public static pure model boolean nullequals(nullable Object o,
      @                                             nullable Object oo) {
      @     return o == oo
      @            || ( o != null && oo != null && o.equals(oo));
      @ }
      @*/

    public static interface Entry {

        //@ public model instance nullable Object abstractKey;
        //@ public model instance nullable Object abstractValue;
		
        /**
         * True iff we are allowed to contain null:
         **/
        //@ instance
        //@   ghost public boolean containsNull;
		
        /*@  public normal_behavior
          @     ensures \result == abstractKey;
          @*/
        /*@ pure nullable @*/ Object getKey();

        /*@  public normal_behavior
          @     ensures \result == abstractValue;
          @*/
        /*@ pure nullable @*/ Object getValue();
		
        /*@ public behavior
          @     assignable this.abstractValue;
          @     ensures \result == \old(this.abstractValue);
          @     ensures this.abstractValue == value;
          @     signals_only NullPointerException, UnsupportedOperationException,
                             ClassCastException, IllegalArgumentException;
          @     signals (NullPointerException) \not_modified(this.abstractValue)
          @             && (abstractValue == null) && !containsNull;
          @     signals (UnsupportedOperationException)
          @               \not_modified(this.abstractValue) 
          @             && (* if the map's put operation is not supported  *);
          @     signals (ClassCastException) \not_modified(this.abstractValue)
          @             && (* \typeof(abstractValue) is incompatible
          @                with the valueType of this map *);
          @     signals (IllegalArgumentException) \not_modified(this.abstractValue)
          @             && (* if some aspect of value is not 
          @                allowed in the map *);
          @*/
        Object setValue(Object value);

        /*+@ also
          @   public normal_behavior
          @     requires o instanceof Entry;
          @     ensures \result == 
          @      (    JMLNullSafe.equals(((Entry)o).abstractKey, abstractKey)
          @        && JMLNullSafe.equals(((Entry)o).abstractValue,
          @                              abstractValue) );
          @+*/
        /*@  also
          @   public normal_behavior
          @     requires !(o instanceof Entry);
          @     ensures \result == false;
          @+*/
        /*-@  also
          @   public normal_behavior
          @     requires o instanceof Entry;
          @     ensures \result == 
          @      (    nullequals(((Entry)o).abstractKey, abstractKey)
          @        && nullequals(((Entry)o).abstractValue, abstractValue) );
          @*/
        /*@ pure @*/ boolean equals(/*@ nullable @*/ Object o);

        /*@ pure @*/ int hashCode();
    }

    /*@
      @ public normal_behavior
      @    requires e != null;
      @    ensures \result <==> contains(e.getKey(),e.getValue());
      @ public pure model boolean contains(Entry e);
      @
      @
      @ public pure model boolean contains(Object key, Object value);
      @*/

    
    /*@ axiom (\forall Map m; (\forall Object k,v,vv; 
                  (m.contains(k,v) && m.contains(k,vv)) ==> nullequals(v,vv)));
      @*/
		
    //+@ public model instance non_null JMLEqualsSet theMap; in objectState;

    /*+@ public instance invariant  
      @      (\forall Object o; theMap.has(o); o instanceof Map.Entry);
      @*/
	   
    /*+@ public instance invariant 	   
      @      (\forall Object o1, o2; theMap.has(o1) && theMap.has(o2); 
      @                             o2!=o1 ==> !JMLNullSafe.equals(o2,o1));
      @*/	   
    
    /**
     * True iff we are allowed to contain null keys and values.
     **/
    //@ instance ghost public boolean containsNull;	

    /*+@ public normal_behavior
      @    ensures \result == theMap.int_size();
      @ implies_that 
      @    ensures \result >= 0;
      @*/
    /*@ pure @*/
    int size();

    /*+@ public normal_behavior
      @    ensures \result <==> theMap.isEmpty(); 
      @  implies_that
      @+*/
    /*@ public normal_behavior
      @    ensures \result <==> (size() == 0); 
      @*/
    /*@ pure @*/ boolean isEmpty();
	
    /*+@ public normal_behavior
      @    ensures \result <==>
      @      (\exists Map.Entry e; theMap.has(e) && e != null; 
      @                            JMLNullSafe.equals(e.abstractKey, key));
      @+*/
    /*-@ public normal_behavior
      @    ensures \result <==>
      @      (\exists Map.Entry e; contains(e); 
      @                            nullequals(e.abstractKey, key));
      @*/
    /*@ pure @*/ boolean containsKey(/*@ nullable @*/ Object key);

    /*+@ public behavior
      @    ensures \result <==>
      @      (\exists Map.Entry e; theMap.has(e) && e != null; 
      @                            JMLNullSafe.equals(e.abstractValue, value));
      @    signals_only ClassCastException, NullPointerException;
      @    signals (ClassCastException)
      @         (* if the value is not appropriate for this object *);
      @    signals (NullPointerException) value == null
      @         && (* this type doesn't permit null values *);
      @*/
    /*-@ public behavior
      @    ensures \result <==>
      @      (\exists Map.Entry e; contains(e); 
      @                            nullequals(e.abstractValue, value));
      @    signals_only ClassCastException, NullPointerException;
      @    signals (ClassCastException)
      @         (* if the value is not appropriate for this object *);
      @    signals (NullPointerException) value == null
      @         && (* this type doesn't permit null values *);
      @*/
    /*@ pure @*/ boolean containsValue(/*@ nullable @*/ Object value);

    /*@   public normal_behavior
      @      requires !containsKey(key);
      @      ensures \result == null;
      @ also
      @*/
    /*+@
      @   public normal_behavior
      @    requires containsKey(key);    
      @    ensures (\exists Entry e; theMap.has(e); e != null
      @            && JMLNullSafe.equals(e.abstractKey, key)
      @            && \result.equals(e.abstractValue));
      @*/
    /*-@
      @ public normal_behavior
      @    requires containsKey(key);    
      @    ensures (\exists Entry e; contains(e);
      @               nullequals(e.abstractKey, key)
      @            && \result == e.abstractValue);
      @    ensures (\forall Entry e; \old(contains(e)) <==> contains(e));
      @*/
    /*@ pure @*/ Object get(/*@ nullable @*/ Object key);

    /*+@ public behavior
      @    assignable objectState;
      @    ensures (\exists Entry e; theMap.has(e); e != null
      @            && JMLNullSafe.equals(e.abstractKey, key)
      @            && JMLNullSafe.equals(e.abstractValue, value));
      @ also
      @+*/
    /*@ public behavior
      @    assignable objectState;
      @    ensures (\exists Entry e; contains(e);
      @               nullequals(e.abstractKey, key)
      @            && nullequals(e.abstractValue, value));
      @    ensures (\forall Entry e; \old(contains(e)) ==> contains(e));
      @    ensures (\forall Entry e; contains(e) ==>
                          (\old(contains(e)) || (e.getKey() == key &&
                                                 e.getValue() == value)));
      @    ensures \result == \old(get(key));
      @*/
    /*+@
      @    signals_only RuntimeException;
      @    signals (NullPointerException) \not_modified(value)
      @             && (key==null)||(value==null) && !containsNull;
      @    signals (UnsupportedOperationException) \not_modified(theMap) 
      @             && (* if the map's put operation is not supported  *);
      @    signals (ClassCastException) \not_modified(theMap)
      @             && (* \typeof(key) or \typeof(value) is incompatible
      @                with the valueType or keyType of this map *);
      @    signals (IllegalArgumentException) \not_modified(theMap)
      @             && (* if some aspect of key or value is not 
      @                allowed in the map *);
      @*/
    Object put(/*@ nullable @*/ Object key, /*@ nullable @*/ Object value);

    /*+@ public behavior
      @    assignable theMap;
      @    ensures \result != null
      @        ==> (\exists Entry e; e != null && \old(theMap.has(e));
      @                      JMLNullSafe.equals(e.abstractKey, key)
      @                   && \result.equals(e.abstractValue)); 
      @    ensures !(\exists Entry e; e != null && \old(theMap.has(e));
      @                      JMLNullSafe.equals(e.abstractKey, key));
      @    signals_only RuntimeException;
      @ also
      @+*/
    /*@ public behavior
      @    assignable objectState;
      @    ensures (\forall Entry e; contains(e) ==> \old(contains(e)));
      @    ensures (\forall Entry e; \old(contains(e));
      @                (contains(e) || nullequals(key, e.getKey())));
      @    ensures \old(containsKey(key)) ==>
      @             nullequals(\result, \old(get(key)));
      @    ensures !\old(containsKey(key)) ==> \result == null;
      @    signals_only RuntimeException;
      @    signals (UnsupportedOperationException)
      @              (* if this operation is not supported *);
      @    signals (ClassCastException)
      @              (* if the argument is not appropriate *);
      @    signals (NullPointerException) key == null
      @              && (* if this map doesn't support null keys *);
      @*/
    /*+@
      @ implies_that
      @    assignable objectState;
      @    ensures !containsKey(key);
      @    ensures (\forall Entry e; theMap.has(e) ==> \old(theMap.has(e)));
      @    ensures (\forall Entry e; \old(theMap.has(e));
      @                (theMap.has(e)
      @                 || JMLNullSafe.equals(e.abstractKey, key)));
      @+*/
    Object remove(/*@ nullable @*/ Object key);

    /*+@  public behavior
      @     assignable theMap;
      @     ensures (\forall Entry e; t.theMap.has(e); 
      @                               theMap.has(e));
      @     signals_only RuntimeException;
      @     signals (NullPointerException) \not_modified(theMap)
      @              && (t == null) && !containsNull;
      @     signals (UnsupportedOperationException) \not_modified(theMap) 
      @              && (* if the map's put operation is not supported  *);
      @     signals (ClassCastException) \not_modified(theMap)
      @              && (* \typeof(t) or is incompatible
      @                 with this map *);
      @     signals (IllegalArgumentException) \not_modified(theMap)
      @              && (* if some aspect of a key or value is not 
      @                 allowed in the map *);
      @ also
      @*/
    /*@ public behavior
           assignable objectState;
           ensures (\forall Entry e; \old(contains(e)) ==> contains(e));
           ensures (\forall Entry e; \old(t.contains(e)) ==> contains(e));
           ensures (\forall Entry e; contains(e) ==> 
                      (\old(contains(e)) || \old(t.contains(e))));
      @    signals_only RuntimeException;
      @*/
    void putAll(Map t);

    /*+@ public behavior
      @    assignable theMap;
      @    ensures theMap.isEmpty();
      @    signals_only RuntimeException;
      @ implies_that
      @+*/
    /*@ public behavior
      @    assignable objectState;
      @    ensures isEmpty();
      @    signals_only RuntimeException;
      @*/
    void clear();

    /*@ public normal_behavior 
      @    ensures_redundantly \result != null;
      @    ensures (\forall Object o; containsKey(o) <==> \result.contains(o));
      @*/
    /*@ pure @*/ Set keySet();

    /*@ public normal_behavior 
      @    ensures \result != null;
      @    ensures (\forall Object o; \result.contains(o) <==> containsValue(o));
      @*/
    /*@ pure @*/ Collection values();

    /*@ public normal_behavior
      @    ensures \result != null;
      @*/
    //+@ ensures \result.theSet.equals(theMap);
    /*@ pure @*/ Set entrySet();

    /*+@ also 
      @  public normal_behavior
      @    requires o instanceof Map;
      @    ensures \result ==> theMap.equals(o);
      @+*/
    /*@ also
      @  public normal_behavior
      @    requires o instanceof Map;
      @    ensures \result
      @         ==> (\forall Entry e; contains(e) <==> ((Map)o).contains(e));
      @ also
      @  public normal_behavior
      @    requires !(o instanceof Map);
      @    ensures \result == false;
      @*/
    /*@ pure @*/ boolean equals(/*@ nullable @*/ Object o);
	
    /*@ pure @*/ int hashCode();
}
