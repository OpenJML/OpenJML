package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.ext.ModifierExtension.ProgramLocation;

import com.sun.tools.javac.util.Name;

public class PureModifier extends ModifierExtension {

    public String jmlKeyword() {
        return "pure";
    }
    
    public Class<?> javaAnnotation() {
        return org.jmlspecs.annotations.Pure.class;
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
