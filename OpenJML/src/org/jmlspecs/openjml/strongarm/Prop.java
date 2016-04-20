package org.jmlspecs.openjml.strongarm;

import com.sun.tools.javac.tree.JCTree.JCExpression;

public class Prop<T extends JCExpression> {

    public T p;
    
    public Prop(T p){
        this.p = p;
    }
    
    public Prop(){}
    
    public void replace(){}
    
    
}
