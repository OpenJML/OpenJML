/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-13
 */
package com.sun.tools.javac.code;

import org.jmlspecs.openjml.ext.JmlPrimitiveTypes.JmlTypeKind;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.List;

/** This class extends Type in order to implement new JML primitive types. */
public class JmlType extends Type {

    /** The token defining the primitive type - 
     * is immutable after construction.
     */
    protected JmlTypeKind jmlClauseKind = null;
    
    final protected Name id;
    
    /** The fully-qualified name of the class used as the runtime
     * representation of this type.
     */
    final public String fqName;
    
    /** The Class used to represent this type in RAC - do not use this
     * value directly since it is lazily initialized in JmlTypes.
     */
    public Symbol.ClassSymbol repSym;
    
    /** Creates a new primitive type with the given token - should be a 
     * singleton for each new JML type */
    // package visibility
    JmlType(JmlTypeKind kind, String fullyQualifiedClassName) {
        super(null);
        jmlClauseKind = kind;
        fqName = fullyQualifiedClassName;
        this.id = null;
    }
    
    /** Creates a new primitive type with the given name - should be a 
     * singleton for each new JML type */
    // package visibility
    JmlType(JmlTypeKind kind, Name id, String fullyQualifiedClassName, List<TypeMetadata> metadata) {
        super(null);
        jmlClauseKind = kind;
        fqName = fullyQualifiedClassName;
        this.id = id;
    }
    
    JmlType(JmlTypeKind token, Name id, String fullyQualifiedClassName) {
    	this(token, id, fullyQualifiedClassName, null);
    }

    
    /** The JmlToken that designates this type */
    public JmlTypeKind jmlClauseKind() {
        return jmlClauseKind;
    }
    
    /** Returns the public name of the type token */
    @Override public String toString() {
        return jmlClauseKind.toString();
    }
    
    // returns true for these new JML primitive types
    @Override public boolean isPrimitive() {
        return true;
    }
    
    // returns true for these new JML primitive types
    @Override public boolean isPrimitiveOrVoid() {
        return true;
    }


    /** The return type is a JDK type, so it is TypeTag.NONE for any JML types. */
    @Override
    public TypeTag getTag() {
        return TypeTag.NONE;
    }
    
    @Override
    public boolean hasTag(TypeTag t) {
        if (t != TypeTag.NONE) return super.hasTag(t);
        return false;
    }

    @Override
    public JmlType cloneWithMetadata(List<TypeMetadata> metadata) {
    	JmlType t = new JmlType(jmlClauseKind, id, fqName, metadata);
    	t.tsym = this.tsym;
    	return t;
    }



}
