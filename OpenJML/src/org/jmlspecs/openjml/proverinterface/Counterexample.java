/**
 * 
 */
package org.jmlspecs.openjml.proverinterface;

import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

/** This class stores variable - value pairs that constitute a counterexample
 * for a given proof attempt.  For flexibility, both variable and value are 
 * stored as Strings.
 * @author David Cok
 *
 */
public class Counterexample implements IProverResult.ICounterexample {
      private SortedMap<String,String> map = new TreeMap<String,String>();
      
      public void put(String key,String value) {
          map.put(key,value);
      }
      
      public String get(String key) {
          return map.get(key);
      }
      
      public Set<Map.Entry<String,String>> sortedEntries() {
          return map.entrySet();
      }
  }