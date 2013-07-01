package com.sun.tools.javac.code;

import org.jmlspecs.openjml.JmlToken;

import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree.JCExpression;

/** This class extends Type in order to implement new JML primitive types. */
public class JmlType extends Type {

    /** The token defining the primitive type - should be considered 
     * immutable after construction.
     */
    protected JmlToken jmlTypeTag;
    
    // Caution do not use directly - lazily initialized in JmlTypes
    Symbol.ClassSymbol repSym;
    
    public JmlType(JmlToken token, TypeSymbol tsym) {
        super(TypeTags.UNKNOWN,tsym);
        jmlTypeTag = token;
    }
    
    public JmlToken jmlTypeTag() {
        return jmlTypeTag;
    }
    
    @Override public String toString() {
        return jmlTypeTag.internedName();
    }
    
    @Override public boolean isPrimitive() {
        return true;
    }

}
