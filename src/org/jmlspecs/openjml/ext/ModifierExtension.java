package org.jmlspecs.openjml.ext;


public abstract class ModifierExtension {

    public boolean isInArray(ProgramLocation loc, ProgramLocation[] locs) {
        for (ProgramLocation p: locs) if (p==loc) return true;
        return false;
    }
    
    
    public abstract String jmlKeyword();
    
    public abstract Class<?> javaAnnotation();
    
    public abstract boolean isAllowed(ProgramLocation loc, boolean isInJML);

    
}
