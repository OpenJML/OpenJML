package com.sun.tools.javac.code;

import org.jmlspecs.openjml.JmlToken;

import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree.JCExpression;


public class JmlType extends Type {

    public JmlToken jmlTypeTag;
    
    public JCExpression repType;
    
    public JmlType(JmlToken token, TypeSymbol tsym) {
        super(TypeTags.UNKNOWN,tsym);
        jmlTypeTag = token;
    }
    
    @Override public String toString() {
        return jmlTypeTag.internedName();
    }
    
    @Override public boolean isPrimitive() {
        return true;
    }

}
