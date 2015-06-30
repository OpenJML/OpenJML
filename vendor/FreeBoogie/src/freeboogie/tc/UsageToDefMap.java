package freeboogie.tc;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import freeboogie.util.Closure;

/**
 * Used to map usage of a name to the deinition of that name.
 * Unlike a simple hash it allows quick retrieval of all usages
 * of a definition.
 *
 * @author rgrig 
 * @author reviewed by TODO
 * @param <U> the type of the usage object
 * @param <D> the type of the definition object
 */
public class UsageToDefMap<U, D> {
   private HashMap<U, D> usageToDef = new HashMap<U, D>();
   private HashMap<D, HashSet<U>> defToUsage = new HashMap<D, HashSet<U>>();
   
   private HashSet<U> getUsages(D d) {
     HashSet<U> u = defToUsage.get(d);
     if (u == null) {
       u = new HashSet<U>();
       defToUsage.put(d, u);
     }
     return u;
   }
   
   /**
    * Connect usage {@code u} to the definition {@code d}.
    * @param u the usage
    * @param d the definition
    */
   public void put(U u, D d) {
     usageToDef.put(u, d);
     HashSet<U> usages = getUsages(d);
     usages.add(u);
     defToUsage.put(d, usages);
   }
   
   /**
    * Add {@code d} as a definition, if not already.
    * @param d the definition
    */
   public void seenDef(D d) {
     getUsages(d);
   }
   
   /**
    * Returns the definition of a usage.
    * @param u the usage
    * @return the definition of {@code u}
    */
   public D def(U u) {
     return usageToDef.get(u);
   }
   
   /**
    * Returns the set of usages of a certaini definition. The user
    * should not modify the result of this function.
    * @param d the definition
    * @return the usages of {@code d}
    */
   public Set<U> usages(D d) {
     return defToUsage.get(d);
   }
   
   /**
    * Returns the number of definitions
    * @return the number of definitions
    */
   public int defCnt() {
     return defToUsage.size();
   }
   
   /**
    * Iterate over usages.
    * @param f the function to be applied to each usage
    */
   public void iterUsage(Closure<U> f) {
     for (U k : usageToDef.keySet()) if (k != null) f.go(k);
   }
   
   /**
    * Iterate over definitions.
    * @param f the function to be applied to each definition
    */
   public void iterDef(Closure<D> f) {
     for (D v : defToUsage.keySet()) if (v != null) f.go(v);
   }
}
