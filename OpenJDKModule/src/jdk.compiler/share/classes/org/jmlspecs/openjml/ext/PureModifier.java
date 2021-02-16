/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;



public class PureModifier extends ModifierExtension {

    // TODO: Use a Name?
    public String jmlKeyword() {
        return "pure";
    }
    
    @Override
    public Class<org.jmlspecs.annotation.Pure> javaAnnotation() {
        return org.jmlspecs.annotation.Pure.class;
    }
    
    static protected ProgramLocation[] locations = 
        { 
            ProgramLocation.TOP_LEVEL_CLASS,
            ProgramLocation.NESTED_CLASS,
            ProgramLocation.LOCAL_CLASS,
            ProgramLocation.METHOD,
            ProgramLocation.CONSTRUCTOR,
        };
    
    public boolean isAllowed(ProgramLocation loc, boolean isInJML) {
        return isInArray(loc,locations);
    }

}
