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
// along with GNU Emacs; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.util;

/** JML's specification of java.util.Map.
 * @version $Revision: 2120 $
 * @author Katie Becker
 * @author Gary T. Leavens
 * @author David R. Cok
 */
public interface Map<K,V> {
    /*@ public normal_behavior
      @   ensures \result == ( o == oo ||
      @        ( o != null && oo != null && o.equals(oo)));
      @ static public model pure boolean nullequals(Object o, Object oo);
      @*/

    //-@ immutable
    /*-@ pure public static model class Content {

          public \bigint theSize;

          // This is object containment (not equals)
          public normal_behavior
            ensures true;
          //-@ function pure
          public Object mapsObject(Object key);


          public normal_behavior
            ensures true;
          //-@ function pure
          public Object maps(Object key);

          public normal_behavior
            ensures true;
          public function pure boolean hasMapObject(Object key);

          public normal_behavior
            ensures true;
          //-@ function pure
          public boolean hasMap(Object key);
        }
      @*/

    /*-@
        public invariant (\forall Object o; content.theSize == 0 ==> 
                      !content.hasMapObject(o));
        public invariant (\forall Object o; content.theSize == 0 ==>
                      !content.hasMap(o));
        public invariant content.theSize == 0 ==> !content.hasMapObject(null);
        public invariant content.theSize == 0 ==> !content.hasMap(null);
      @*/
    /*-@ axiom (\forall Content c; (\forall Object o;
                   c.hasMapObject(o) ==> c.hasMap(o)));
        axiom (\forall Content c; c.hasMapObject(null) <==> c.hasMap(null));
        axiom (\forall Content c; (\forall Object o;
                   c.hasMapObject(o) ==> c.mapsObject(o) == c.maps(o)));
        axiom (\forall Content c;
                   c.hasMapObject(null) ==> c.mapsObject(null) == c.maps(null));
     */
          
    //-@ public model instance non_null Content content; in objectState;
    //-@ public invariant content.owner == this;

    /*-@ public normal_behavior
      @   ensures \result <==> ( 
             content != null &&
             content.theSize == 0  && 
             (\forall Object o; !content.hasMapObject(o)) &&
             (\forall Object o; !content.hasMap(o)) &&
             !content.hasMapObject(null) &&
             !content.hasMap(null) 
             );
      @*/
    /*@ model pure public boolean initialMap();
      @*/

    public static interface Entry<K,V> {

        //@ public model instance K abstractKey;
        //@ public model instance V abstractValue;
		
        /*@  public normal_behavior
          @     ensures \result == abstractKey;
          @*/
        /*@ pure @*/ K getKey();

        /*@  public normal_behavior
          @     ensures \result == abstractValue;
          @*/
        /*@ pure @*/ V getValue();
		
        /*@ public behavior
          @     assignable this.abstractValue;
          @     ensures \result == \old(this.abstractValue);
          @     ensures this.abstractValue == value;
          @
          @   // FIXME - fix these exceptions
          @     signals_only NullPointerException, UnsupportedOperationException,
                               ClassCastException, IllegalArgumentException;
          @     signals (NullPointerException) \not_modified(this.abstractValue);
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
        V setValue(V value);

        /*@  also
          @   public normal_behavior
          @     requires o instanceof Entry;
          @     ensures \result ==  ( this == o ||
          @      (    nullequals(((Entry)o).abstractKey, abstractKey)
          @        && nullequals(((Entry)o).abstractValue, abstractValue) ));
          @  also
          @   public normal_behavior
          @     requires !(o instanceof Entry);
          @     ensures \result == false;
          @*/
        /*@ pure @*/ boolean equals(Object o);

        /*@ pure @*/ int hashCode();

        /*@ public normal_behavior
          @   ensures \result <==> (nullequals(abstractKey,key) &&
          @                         nullequals(abstractValue, value));
          @ public pure model boolean equals(Object key, Object value);
          @
          @
          @ public normal_behavior
          @   ensures \result <==> (abstractKey == key &&
          @                         abstractValue == value);
          @ public pure model boolean equalsObjects(Object key, Object value);
          @
          @
          @ public normal_behavior
          @   ensures \result <==> equalsObjects(e.getKey(),e.getValue());
          @ public pure model boolean equalsObjects(Entry e);
          @*/
    }

    //@ public normal_behavior
    //@   ensures (* \result == content.theSize *);
    //-@   ensures \result == content.theSize;
    /*@ pure @*/
    int size();

    /*-@ public normal_behavior
      @    ensures \result <==> (content.theSize == 0); 
      @*/
    /*@ pure @*/ boolean isEmpty();
	
    /*-@ public behavior
      @    ensures isEmpty() ==> !\result;
      @    ensures content.hasMap(key) <==> \result;
      @
      @    signals_only ClassCastException, NullPointerException;
           // FIXME - fix exceptions
      @    signals (ClassCastException)
      @         (* if the value is not appropriate for this object *);
      @    signals (NullPointerException) key == null
      @         && (* this type doesn't permit null values *);
      @*/
    /*@ pure @*/ boolean containsKey(Object key) throws RuntimeException;

    /*-@ public behavior
      @    ensures isEmpty() ==> !\result;
      @    ensures \result <==> (
              nullequals(value,content.mapsObject(null)) ||
              (\exists Object k; nullequals(value,content.mapsObject(k))));
      @
           // FIXME - fix exceptions
      @    signals_only ClassCastException, NullPointerException;
      @    signals (ClassCastException)
      @         (* if the value is not appropriate for this object *);
      @    signals (NullPointerException) value == null
      @         && (* this type doesn't permit null values *);
      @*/
    /*@ pure @*/ boolean containsValue(Object value);

    /*-@ public normal_behavior
      @    requires !content.hasMap(key);// hasMap or hasMapObject -- FIXME
      @    ensures \result == null;
      @ also public normal_behavior
      @    requires content.hasMap(key);    // hasMap or hasMapObject -- FIXME
      @    ensures \result == content.maps(key);
      @ also public normal_behavior
      @    requires content.hasMapObject(key);
      @    ensures \result == content.mapsObject(key);

           // FIXME - exceptions?
      @*/
    /*@ pure @*/ V get(Object key);

    /*-@ public behavior
      @    assignable objectState;
      @    ensures content.hasMap(key);
      @    ensures !isEmpty() && containsKey(key) && containsValue(value);
      @    ensures content.mapsObject(key) == value;
      @    ensures content.maps(key) == value;
      @    ensures \result == \old(get(key));

      @    ensures (\forall Object k; k != key ==> 
                        (\old(content.hasMapObject(k)) 
                                       == content.hasMapObject(k)));
      @    ensures key != null ==> (\old(content.hasMapObject(null)) 
                                       == content.hasMapObject(null));

      @
      @    ensures (\forall Object k; k.equals(key) ==> content.hasMap(k));
      @    ensures (\forall Object k; \old(!k.equals(key)) ==> 
                        (\old(content.hasMap(k)) == content.hasMap(k)));
      @    ensures key != null ==> (\old(content.hasMap(null)) 
                                       == content.hasMap(null));
      @
      @    ensures (\forall Object k; k.equals(key) ==> content.maps(k) == value);
      @    ensures (\forall Object k; \old(!k.equals(key)) ==> 
                        \old(content.maps(k)) == content.maps(k));
      @    ensures key != null ==> 
                        \old(content.maps(null)) == content.maps(null);
      @
      @    ensures (\forall Object k; \old(!k.equals(key)) ==> 
                        \old(content.mapsObject(k)) == content.mapsObject(k));
      @    ensures key != null ==> \old(content.mapsObject(null)) 
                                       == content.mapsObject(null);
      @*/
    /* FIXME @
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
    V put(K key, V value);

    /*-@ public behavior
      @    assignable objectState;
      @    ensures !content.hasMapObject(key);
      @    ensures !content.hasMap(key);
      @    ensures !containsKey(key);
      @    ensures (\forall Object k; \old(!k.equals(key)) ==> 
                        \old(content.mapsObject(k)) == content.mapsObject(k));
      @    ensures key != null ==> 
                        \old(content.mapsObject(null)) == content.mapsObject(null);
      @    ensures \result == \old(get(key));
      @*/
    /*@ // FIXME
      @    signals_only ClassCastException, NullPointerException,
                               UnsupportedOperationException;
      @    signals (UnsupportedOperationException)
      @              (* if this operation is not supported *);
      @    signals (ClassCastException)
      @              (* if the argument is not appropriate *);
      @    signals (NullPointerException) key == null
      @              && (* if this map doesn't support null keys *);
      @*/
    V remove(Object key);

    /*@ public behavior
           requires t != null;
           assignable objectState;
           ensures \old(isEmpty() && t.isEmpty()) <==> isEmpty();
           ensures (\forall Object k; \old(t.containsKey(k) || containsKey(k)) 
                                       <==> containsKey(k));
           ensures (\forall Object k; \old(t.containsKey(k)) ==>  
                                              t.get(k) == get(k));
           ensures (\forall Object k; \old(containsKey(k) && !t.containsKey(k))
                                              ==> get(k) == \old(get(k)));
        also public exceptional_behavior
           requires t == null;
           assignable \nothing;
           signals_only NullPointerException;
      @*/
     /*  FIXME
      @    signals (NullPointerException) \not_modified(theMap)
      @             && (t == null);
      @    signals (UnsupportedOperationException) \not_modified(theMap) 
      @             && (* if the map's put operation is not supported  *);
      @    signals (ClassCastException) \not_modified(theMap)
      @             && (* \typeof(t) or is incompatible
      @                with this map *);
      @    signals (IllegalArgumentException) \not_modified(theMap)
      @             && (* if some aspect of a key or value is not 
      @                allowed in the map *);
      @*/
    void putAll(Map<? extends K, ? extends V> t);

    /*-@ public normal_behavior
      @    assignable objectState;
      @    ensures isEmpty();
      @    ensures (\forall Object k; !content.hasMapObject(k));
      @*/
    void clear();

    /*@ public normal_behavior 
      @    ensures \result != null;
           // FIXME
      @*/
    /*@ pure @*/ Set<K> keySet();

    /*@ public normal_behavior 
      @    ensures \result != null;
           // FIXME
      @*/
    /*@ pure @*/ Collection<V> values();

    /*@ public normal_behavior
      @    ensures \result != null; 
           // FIXME
      @*/
    /*@ pure @*/ Set<Entry<K,V>> entrySet();

    /*@
      @ also
      @  public normal_behavior
      @    requires (o instanceof Map);
      @    ensures \result == this.entrySet().equals( ((Map)o).entrySet() );
      @ also public normal_behavior
      @    requires !(o instanceof Map);
      @    ensures !\result;
      @*/
    /*@ pure @*/ boolean equals(Object o);
	
    /*@ pure @*/ int hashCode();
}
