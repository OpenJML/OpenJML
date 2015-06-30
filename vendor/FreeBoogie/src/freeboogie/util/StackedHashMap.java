package freeboogie.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

/**
 * It implements the {@code Map} interface but also has
 * methods {@code push} and {@code pop}, the latter removing
 * all the bindings added since the last push; bindings
 * that existed before the push but were overriden after
 * will return to their previous state. The {@code Map}
 * intefrace is not exactly followed. The methods {@code keySet},
 * {@code values}, and {@code entrySet} are just copies and changes
 * in them do not reflect in the map, or viceversa.
 * 
 * See the {@code main} method for some examples.
 *
 * @param <K> the type of the key
 * @param <V> the type of the values
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class StackedHashMap<K, V> implements Map<K, V> {
  // there is always a first element in |data|
  private LinkedList<LinkedHashMap<K, V>> data;
  
  /**
   * Constructs a new {@code StackedHashMap}.
   */
  public StackedHashMap() {
    clear();
  }
  
  /**
   * Marks this place so that all the key-value bindings
   * afterwards can be removed quickly with one {@code pop()}
   * operation.
   */
  public void push() {
    data.addFirst(new LinkedHashMap<K, V>());
  }

  /**
   * Removes all the bindings that were added since the last
   * {@code push}. If there is no previous {@code push} then
   * it is equivalent to {@code clear}.
   */
  public void pop() {
    if (data.size() > 1) data.removeFirst();
    else clear();
  }

  /* @see java.util.Map#clear() */
  public void clear() {
    data = new LinkedList<LinkedHashMap<K, V>>();
    data.addFirst(new LinkedHashMap<K, V>());
  }

  /* @see java.util.Map#containsKey(java.lang.Object) */
  public boolean containsKey(Object key) {
    for (LinkedHashMap<K, V> h : data)
      if (h.containsKey(key)) return true;
    return false;
  }

  /* @see java.util.Map#containsValue(java.lang.Object) */
  public boolean containsValue(Object value) {
    for (LinkedHashMap<K, V> h : data)
      if (h.containsValue(value)) return true;
    return false;
  }

  /* @see java.util.Map#entrySet() */
  public Set<java.util.Map.Entry<K, V>> entrySet() {
    HashSet<K> seen = new HashSet<K>();
    Set<Map.Entry<K, V>> s = new HashSet<Map.Entry<K, V>>();
    for (LinkedHashMap<K, V> h : data) {
      for (Map.Entry<K, V> e : h.entrySet()) if (!seen.contains(e.getKey())) {
        seen.add(e.getKey());
        s.add(e);
      }
    }
    return s;
  }

  /* @see java.util.Map#get(java.lang.Object) */
  public V get(Object key) {
    for (LinkedHashMap<K, V> h : data) {
      V v = h.get(key);
      if (v != null) return v;
    }
    return null;
  }

  /* @see java.util.Map#isEmpty() */
  public boolean isEmpty() {
    return size() == 0;
  }

  /* @see java.util.Map#keySet() */
  public Set<K> keySet() {
    Set<K> s = new HashSet<K>();
    for (LinkedHashMap<K, V> h : data)
      s.addAll(h.keySet());
    return s;
  }

  /* @see java.util.Map#put(java.lang.Object, java.lang.Object) */
  public V put(K key, V value) {
    return data.getFirst().put(key, value);
  }

  /* @see java.util.Map#putAll(java.util.Map) */
  public void putAll(Map<? extends K, ? extends V> map) {
    data.getFirst().putAll(map);
  }

  /* @see java.util.Map#remove(java.lang.Object) */
  public V remove(Object key) {
    V r = null;
    for (LinkedHashMap<K, V> h : data) {
      V v = h.remove(key);
      if (r == null) r = v;
    }
    return r;
  }

  /* @see java.util.Map#size() */
  public int size() {
    int sz = 0;
    for (LinkedHashMap<K, V> h : data) sz += h.size();
    return sz;
  }

  /* @see java.util.Map#values() */
  public Collection<V> values() {
    ArrayList<V> v = new ArrayList<V>();
    for (LinkedHashMap<K, V> h : data) v.addAll(h.values());
    return v;
  }
  
  /**
   * To be used for debug.
   * @param <K> the key type
   * @param <V> the value type
   * @param s the stacked hash map to print
   */
  public static <K, V> void print(StackedHashMap<K, V> s) {
    System.out.println("--- begin map ---");
    for (Map.Entry e : s.entrySet())
      System.out.println("" + e.getKey() + " -> " + e.getValue());
    System.out.println("--- end map ---");
  }

  /**
   * @param args
   */
  public static void main(String[] args) {
    StackedHashMap<Character, Integer> test = 
      new StackedHashMap<Character, Integer>();
    test.put('a', 0);
    test.put('b', 1);
    test.put('c', 2);
    test.push();
    test.put('c', 3);
    test.put('d', 4);
    print(test); // a->0, b->1, c->3, d->4
    test.remove('b');
    print(test); // a->0, c->3, d->4
    test.pop();
    print(test); // a->0, c->2
    test.pop();
    print(test); // empty
    test.pop();
    print(test); // still empty
    test.put('a', 5);
    print(test); // a->5
  }

}
