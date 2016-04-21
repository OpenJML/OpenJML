package org.jmlspecs.openjml.strongarm;

import org.jmlspecs.openjml.JmlTreeUtils;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;

public class Prop<T extends JCExpression> {

    public T p;
    
    public Prop(T p){
        this.p = p;
    }
    
    public Prop(){}
    
    public void replace(){}
    
    public JCExpression toTree(JmlTreeUtils treeutils){
        return p;
    }
    
}
