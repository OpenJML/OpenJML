package org.jmlspecs.openjml.strongarm;

import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;

import com.sun.tools.javac.tree.JCTree.JCExpression;

public class TraceElement {
    private List<JCExpression> exprs = new ArrayList<JCExpression>();
    private BasicBlock block;
    public TraceElement(BasicBlock block){
        this.block = block;
    }
    
    public void addExpr(JCExpression expr){
        exprs.add(expr);
    }
    
    public BasicBlock getBlock(){
        return this.block;
    }
    public List<JCExpression> getExprs(){
        return this.exprs;
    }
}
