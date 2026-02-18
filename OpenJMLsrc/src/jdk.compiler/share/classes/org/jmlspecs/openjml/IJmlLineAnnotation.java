package org.jmlspecs.openjml;

import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;

public abstract class IJmlLineAnnotation extends JmlAbstractStatement {
    abstract public IJmlClauseKind clauseKind();
    
    public int line; 
    public int line() { return line; }
    public java.util.List<JCExpression> exprs() { return null; }
}
