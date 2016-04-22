package org.jmlspecs.openjml.strongarm;

import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.strongarm.transforms.SubstituteTree;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCUnary;

public class Prop<T extends JCExpression> {

    public T p;
    
    public Prop(T p){
        this.p = p;
    }
    
    public Prop(){}
    
    public void replace(JCTree replacement){
        SubstituteTree.replace(replacement, p);
    }
    
    public JCExpression toTree(JmlTreeUtils treeutils){
        return p;
    }
    
}
