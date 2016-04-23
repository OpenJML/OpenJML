package org.jmlspecs.openjml.strongarm;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.strongarm.transforms.SubstituteTree;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.util.List;

public class Prop<T extends JCExpression> {

    public T p;
    
    public Prop(T p){
        this.p = p;
    }
    
    public Prop(){}
    
    public void replace(JCTree replacement){
        
        JCExpression e = SubstituteTree.replace(replacement, p);
        
        if(e!=null){
            p = (T) e;
        }
    }
    
    public List<JmlMethodClause> getClauses(List<JmlMethodClause> clauses, JmlTreeUtils treeutils, JmlTree.Maker M){
        
        JmlMethodClauseExpr clause = M.JmlMethodClauseExpr
                (
                        JmlToken.REQUIRES,  
                        p
                );
        
        return clauses.append(clause);
    }
    
    public JCExpression toTree(JmlTreeUtils treeutils){
        return p;
    }
    
}
