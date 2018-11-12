/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

/** Any class that contains JML extensions to be registered in the keyword recognizer
 *  must implement this marker interface*/
public interface JmlExtension {

    /** Returns a list of clause type objects that sre the extensions provided by
     *  this derived class of JmlExtension
     */
    IJmlClauseType[] clauseTypes(); 
    
    /** This marker interface marks classes that contain extensions that are new
     *  type clauses (like invariant) */
    public static interface TypeClause extends JmlExtension {}
    
    /** This marker interface marks classes containing extensions that are
     *  new method specification clauses (like requires). */
    public static interface MethodClause extends JmlExtension {}

    /** This marker interface marks classes that contain extensions that are new
     *  JML statements clauses (like assert) */
    public static interface Statement extends JmlExtension {}

}
