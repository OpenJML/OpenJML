/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

public class Dependencies {
    // FIXME - The computing and handling of dependencies needs reworking.
    // The map in this class is static, because otherwise the information
    // is lost from one compilation context to another.  However, this way it
    // keeps accumulating information forever and will hold on to everything else
    // in the system, and run out of memory.  Need a better solution.
    // OK for command-line tools but not for the api or Eclipse.
    // 

    /** The key to use to retrieve the instance of this class from the Context object. */
    /*@ non_null */
    public static final Context.Key<Dependencies> dependenciesKey =
        new Context.Key<Dependencies>();

    /** A method that returns the unique instance of this class for the given Context
     * (creating it if it does not already exist).
     * 
     * @param context the Context whose JmlSpecs instance is wanted
     * @return the singleton instance (per Context) of this class
     */
    public static @NonNull Dependencies instance(@NonNull Context context) {
        Dependencies instance = context.get(dependenciesKey);
        if (instance == null) {
            instance = new Dependencies(context);  // registers itself
        }
        return instance;
    }


    /** Creates an instance in association with the given Context
     *  - do not call the constructor 
     * directly.
     * 
     * @param context The compilation context
     */
    protected Dependencies(@NonNull Context context) {
        context.put(dependenciesKey, this); // register itself
        if (dependsOnMap == null) dependsOnMap = new HashMap<JavaFileObject, Set<JavaFileObject>>();
        // NOTE: Although you might get away with it, the goal is to have
        // this class be independent of all the other tools
    }
    
    /** The map holding the set of things that a given object affects.
     * 
     */
    @NonNull
    static protected Map<JavaFileObject,Set<JavaFileObject>> dependsOnMap = null;
    
    /** Record that item a needs to be recompiled if b changes */
    public void dependsOn(@NonNull JavaFileObject a, @NonNull JavaFileObject b) {
        if (Utils.ifSourcesEqual(a, b)) return;
        Set<JavaFileObject> t = dependsOnMap.get(b);
        if (t == null) dependsOnMap.put(b, t = new HashSet<JavaFileObject>());
        t.add(a);
    }
    
    /** Record that item a needs to be recompiled if anything in array b changes */
    public void dependsOn(@NonNull JavaFileObject a, @NonNull JavaFileObject[] b) {
        for (JavaFileObject bb: b) dependsOn(a,bb);
    }
    
    /** Record that item a needs to be recompiled if anything in array b changes */
    public void dependsOn(@NonNull JavaFileObject a, @NonNull List<JavaFileObject> b) {
        for (JavaFileObject bb: b) dependsOn(a,bb);
    }
    
    /** Record that item a needs to be recompiled if anything in array b changes */
    public void dependsOn(@NonNull JavaFileObject a, @NonNull Collection<JavaFileObject> b) {
        for (JavaFileObject bb: b) dependsOn(a,bb);
    }
    
    /** Returns a Set of items potentially affected if the argument is changed.
     * A null result is equivalent to an empty set. */
    public @Nullable Set<JavaFileObject> getAffected(@NonNull JavaFileObject a) {
        return dependsOnMap.get(a);
    }
}
