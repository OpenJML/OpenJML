/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.annotation.Pure;

/** This class implements an extensible enum class holding values representing
 * the locations in a program that JML modifiers can appear.  Additional values
 * can be added by creating a new Program Location.  We use singletons
 * so that reference equality can be used.
 * 
 * @author David Cok
 */
@Pure
public class ProgramLocation {
    /** A counter used to give a unique index to each instance of a ProgramLocation.
     * The index is used to be able to create efficient sets as arrays
     * similar to EnumSet. (TODO - not yet implemented)
     */
    static private int counter = 0;
    
    /** The internal, unique index of this instance */
    final public int index;
    
    /** A String to be used to print out an identifying string */
    final public String name;
    
    /** Constructor - use only to create a single instance for each different
     * program location. 
     * @param name An identifying String, used only for human consumption
     */
    public ProgramLocation(String name) {
        index = ++counter;
        this.name = name;
    }
    // equals is reference equality, like Object
    
    public String toString() {
        return name;
    }
    
    public int index() { return index; }
    
    final static public ProgramLocation TOP_LEVEL_CLASS = new ProgramLocation("TOP_LEVEL_CLASS");
    final static public ProgramLocation TOP_LEVEL_INTERFACE = new ProgramLocation("TOP_LEVEL_INTERFACE");
    final static public ProgramLocation NESTED_CLASS = new ProgramLocation("NESTED_CLASS");
    final static public ProgramLocation NESTED_INTERFACE = new ProgramLocation("NESTED_INTERFACE");
    final static public ProgramLocation LOCAL_CLASS = new ProgramLocation("LOCAL_CLASS");
    final static public ProgramLocation LOCAL_INTERFACE = new ProgramLocation("LOCAL_INTERFACE");
    final static public ProgramLocation METHOD = new ProgramLocation("METHOD");
    final static public ProgramLocation CONSTRUCTOR = new ProgramLocation("CONSTRUCTOR");
    final static public ProgramLocation CLASS_FIELD = new ProgramLocation("CLASS_FIELD");
    final static public ProgramLocation INTERFACE_FIELD = new ProgramLocation("INTERFACE_FIELD");
    final static public ProgramLocation FORMAL_PARAMETER = new ProgramLocation("FORMAL_PARAMETER");
    final static public ProgramLocation LOCAL_VARIABLE = new ProgramLocation("LOCAL_VARIABLE");
    
    // anonymous class
}