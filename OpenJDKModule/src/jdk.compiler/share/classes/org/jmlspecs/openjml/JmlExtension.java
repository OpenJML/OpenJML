/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import com.sun.tools.javac.util.Context;

/** Any class that contains JML extensions to be registered in the keyword recognizer
 *  must implement this marker interface*/
public abstract class JmlExtension {

    public Context context;
        
    /** Derived classes can implement specific actions to be performed when registered */
    public void register() {}
    
    public void register(Context context) {
        this.context = context;
        register();
    }
    
    public void synonym(String s, IJmlClauseKind t) {
        Extensions.allKinds.put(s,t);
    }

}
