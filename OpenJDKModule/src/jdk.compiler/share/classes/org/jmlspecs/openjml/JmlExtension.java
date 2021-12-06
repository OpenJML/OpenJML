/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

/** Any class that contains JML extensions to be registered in the keyword recognizer
 *  must implement this marker interface*/
public abstract class JmlExtension {
	protected JmlExtension() {}
    
    public static void synonym(String s, IJmlClauseKind t) {
        Extensions.allKinds.put(s,t);
    }

}
