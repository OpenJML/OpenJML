/**
 * 
 */
package org.jmlspecs.openjml.proverinterface;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import com.sun.tools.javac.tree.JCTree;

/** This class stores variable - value pairs that constitute a counterexample
 * for a given proof attempt.  For flexibility, both variable and value are 
 * stored as Strings.
 * @author David Cok
 *
 */
public class Counterexample implements IProverResult.ICounterexample {
    public SortedMap<String,String> map = new TreeMap<String,String>(); // FIXME - fix visibility
    public Map<JCTree,String> mapv = new HashMap<JCTree,String>(); // FIXME - ditto
    private List<IProverResult.Span> path;
    
    public void put(String key,String value) {
        map.put(key,value);
    }
    
    public void putMap(Map<String,String> map) {
        this.map.putAll(map);
    }
    
    public Map<String,String> getMap() {
        return this.map;
    }

    public void put(JCTree expr,String value) {
        mapv.put(expr,value);
    }

    public String get(String key) {
        return map.get(key);
    }

    public String get(JCTree expr) {
        return mapv.get(expr);
    }

    public Set<Map.Entry<String,String>> sortedEntries() {
        return map.entrySet();
    }
    
    public void putPath(List<IProverResult.Span> path) {
        this.path = path;
    }
    
    public List<IProverResult.Span> getPath() {
        return path;
    }
}