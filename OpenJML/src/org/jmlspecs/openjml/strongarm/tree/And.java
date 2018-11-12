package org.jmlspecs.openjml.strongarm.tree;

import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;

import java.util.ArrayList;
import java.util.Map;
import java.util.Stack;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.strongarm.InferenceAbortedException;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.List;

public class And<T extends JCExpression> extends Prop<T> implements Cloneable, IPropElement {

    public Prop<T> p1;
    public Prop<T> p2;
    
    public And(Prop<T> p1, Prop<T> p2){
        this.p1 = (Prop<T>)p1.clone();
        this.p2 = (Prop<T>)p2.clone();
    }
   
    public static <E extends JCExpression> And<E> of(Prop<E> p1, Prop<E> p2){
        return new And<E>(p1, p2);
    }
    
    public void replace(ArrayList<JCTree> mappings) throws InferenceAbortedException{
        p1.replace(mappings);
        p2.replace(mappings);        
    }
    
    public void replace(Map<JCIdent, ArrayList<JCTree>> mappings, boolean limitDepth) throws InferenceAbortedException{
        p1.replace(mappings, limitDepth);
        p2.replace(mappings, limitDepth);
    }
 
    @Override
    public Object clone(){
        
        //And<T> cloned = new And((Prop<T>)p1.clone(), (Prop<T>)p2.clone());
        
        
        And<T> cloned = new And(p1, p2);
        
        return cloned;
    }
    
    public Map<Prop,String> freeze(Map<Prop,String> m){
        m = p1.freeze(m);
        m = p2.freeze(m);
        
        return m;
    }
    
    // # f = a & (b | (c & d))
    public String toPyEDA(EDAConverter map){
        
        String s1 = p1.toPyEDA(map);
        String s2 = p2.toPyEDA(map);
        
        
        return String.format("(%s & %s)", s1, s2);
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
        return treeutils.makeBinary(0, JCTree.Tag.AND, p1.toTree(treeutils), p2.toTree(treeutils));
    }
    
    @Override
    public void accept(IPropElementVisitor visitor) {        
        visitor.visitAnd(this);
    }
    
}
