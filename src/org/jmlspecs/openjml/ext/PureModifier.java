package org.jmlspecs.openjml.ext;


import com.sun.tools.javac.util.Name;

public class PureModifier extends ModifierExtension {

    public String jmlKeyword() {
        return "pure";
    }
    
    public Class<?> javaAnnotation() {
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
