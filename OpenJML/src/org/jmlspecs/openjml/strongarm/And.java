package org.jmlspecs.openjml.strongarm;

import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.List;

public class And<T extends JCExpression> extends Prop<T> {

    public Prop<T> p1;
    public Prop<T> p2;
    
    public And(Prop<T> p1, Prop<T> p2){
        this.p1 = p1;
        this.p2 = p2;
    }
  
    public static <E extends JCExpression> And<E> of(Prop<E> p1, Prop<E> p2){
        return new And<E>(p1, p2);
    }
    
    public void replace(JCTree replacement){
        p1.replace(replacement);
        p2.replace(replacement);
    }
  
    public List<JmlMethodClause> getClauses(List<JmlMethodClause> clauses, JmlTreeUtils treeutils, JmlTree.Maker M){

        
        List<JmlMethodClause> m1 = p1.getClauses(clauses, treeutils, M);
        List<JmlMethodClause> m2 = p2.getClauses(clauses, treeutils, M);
        
        if(clauses==null){
            return m1.appendList(m2);
        }
        return clauses.appendList(m1.appendList(m2));
    }
    
    public JCExpression toTree(JmlTreeUtils treeutils){
        return treeutils.makeBinary(0, JCTree.AND, p1.toTree(treeutils), p2.toTree(treeutils));
    }
    
}
