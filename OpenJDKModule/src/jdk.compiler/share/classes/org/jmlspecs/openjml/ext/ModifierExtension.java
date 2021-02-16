/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.annotation.Nullable;

import com.sun.tools.javac.util.Context;

// TODO: Complete, use and document

public abstract class ModifierExtension {

    /** Helper function that returns true if the given loc is in the given array. */
    public boolean isInArray(ProgramLocation loc, ProgramLocation[] locs) {
        for (ProgramLocation p: locs) if (p==loc) return true;
        return false;
    }
    
    /** Returns the keyword representing the modifier, or null if there is none (only an annotation) */
    public abstract @Nullable String jmlKeyword();
    
    /** Returns the Class object for the Annotation class that represents this modifier. */
    public abstract @Nullable Class<?> javaAnnotation();
    
    /** Returns true if the modifier is allowed at the given location. */
    public abstract boolean isAllowed(ProgramLocation loc, boolean isInJML);

    
}
