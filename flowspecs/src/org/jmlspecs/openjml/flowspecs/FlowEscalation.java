package org.jmlspecs.openjml.flowspecs;

import com.sun.tools.javac.tree.JCTree.JCExpression;

public class FlowEscalation {
    
    private SecurityType type;
    private JCExpression expr;
    
    public FlowEscalation(SecurityType type, JCExpression expr){
        this.type = type;
        this.expr = expr;
    }

    public SecurityType getType() {
        return type;
    }

    public void setType(SecurityType type) {
        this.type = type;
    }

    public JCExpression getExpr() {
        return expr;
    }

    public void setExpr(JCExpression expr) {
        this.expr = expr;
    }
    
    
    

}
