package org.jmlspecs.openjml.ext;

import org.jmlspecs.annotations.Pure;

import com.sun.tools.javac.util.Name;

public abstract class ModifierExtension {

    static public class ProgramLocation {
        static private int counter = 0;
        final public int index;
        public ProgramLocation() {
            index = ++counter;
        }
        // equals is reference equality, like Object
        
        @Pure
        public int index() { return index; }
        
        final static public ProgramLocation TOP_LEVEL_CLASS = new ProgramLocation();
        final static public ProgramLocation TOP_LEVEL_INTERFACE = new ProgramLocation();
        final static public ProgramLocation NESTED_CLASS = new ProgramLocation();
        final static public ProgramLocation NESTED_INTERFACE = new ProgramLocation();
        final static public ProgramLocation LOCAL_CLASS = new ProgramLocation();
        final static public ProgramLocation LOCAL_INTERFACE = new ProgramLocation();
        final static public ProgramLocation METHOD = new ProgramLocation();
        final static public ProgramLocation CONSTRUCTOR = new ProgramLocation();
        final static public ProgramLocation CLASS_FIELD = new ProgramLocation();
        final static public ProgramLocation INTERFACE_FIELD = new ProgramLocation();
        final static public ProgramLocation FORMAL_PARAMETER = new ProgramLocation();
        final static public ProgramLocation LOCAL_VARIABLE = new ProgramLocation();
        
        // anonymous class
    }
    
    public boolean isInArray(ProgramLocation loc, ProgramLocation[] locs) {
        for (ProgramLocation p: locs) if (p==loc) return true;
        return false;
    }
    
    
    public abstract String jmlKeyword();
    
    public abstract Class<?> javaAnnotation();
    
    public abstract boolean isAllowed(ProgramLocation loc, boolean isInJML);

}
