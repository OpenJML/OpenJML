/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

/** This is an interface for the behavior of options. */
public interface IOption {

    /** The name of the option, as used on the command-line
     * @return The name of the option, as used on the command-line
     */
    /*@ non_null */
    public String optionName();
    
    /** Whether the option takes a required argument
     * @return Whether the option takes a required argument
     */
    public boolean hasArg();
    
    /** The default value of the option
     * @return The default value of the option
     */
    /*@ nullable */
    public Object defaultValue();
    
    /** The help string for the option
     * @return The help string for the option
     */
    /*@ non_null */
    public String help();
    
    /** The canonical form for the option */
    /*@ nullable */
    public String synonym();
    
    /* Whether the option is obsolete */
    public boolean obsolete();

}
