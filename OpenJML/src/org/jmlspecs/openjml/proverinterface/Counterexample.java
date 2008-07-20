/**
 * 
 */
package org.jmlspecs.openjml.proverinterface;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.Map.Entry;

public class Counterexample implements IProverResult.Item {
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