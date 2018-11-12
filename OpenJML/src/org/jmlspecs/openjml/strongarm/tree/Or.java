package org.jmlspecs.openjml.strongarm.tree;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Map;

import com.sun.tools.javac.parser.JmlToken;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.strongarm.InferenceAbortedException;
import org.jmlspecs.openjml.strongarm.JDKListUtils;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.List;

public class Or<T extends JCExpression> extends Prop<T> implements Cloneable, IPropElement {

    public Prop<T> p1;
    public Prop<T> p2;
    
    public Or(Prop<T> p1, Prop<T> p2){
        this.p1 = p1; //(Prop<T>) p1.clone();
        this.p2 = (Prop<T>) p2.clone();
    }
    
    public void replace(Map<JCIdent, ArrayList<JCTree>> mappings, boolean limitDepth) throws InferenceAbortedException{
        p1.replace(mappings, limitDepth);
        p2.replace(mappings, limitDepth);
    }
    
    public void replace(ArrayList<JCTree> mappings) throws InferenceAbortedException{
        p1.replace(mappings);
        p2.replace(mappings);        
    }

    @Override
    public Object clone(){
        
        //Or<T> cloned = new Or((Prop<T>)p1.clone(), (Prop<T>)p2.clone());
        Or<T> cloned = new Or(p1,p2);
        
        return cloned;
    }
    
    
    // # f = a & (b | (c & d))
    public String toPyEDA(EDAConverter map){
        
        String s1 = p1.toPyEDA(map);
        String s2 = p2.toPyEDA(map);
        
        
        return String.format("(%s | %s)", s1, s2);
        
        
    }
    
    public static <E extends JCExpression> Or<E> of(Prop<E> p1, Prop<E> p2){
        return new Or<E>(p1, p2);
    }
    
    public List<JmlMethodClause> getClauses(List<JmlMethodClause> clauses, JmlTreeUtils treeutils, JmlTree.Maker M){
//
//        .tail = JmlMethodClauseGroup
//
//                .cases = List<JmlSpecificationCase>
//                .pos = 0
//                .sourcefile = 0;
//                .token = JmlToken.SPEC_GROUP_START
//                .type==null
//

        List<JmlMethodClause> lhs = p1.getClauses(clauses,  treeutils,  M);
        List<JmlMethodClause> rhs = p2.getClauses(clauses,  treeutils,  M);

        // sort each of the cases
        
        lhs = JDKListUtils.sort(lhs, new ContractComparator());
        rhs = JDKListUtils.sort(rhs, new ContractComparator());
        
        JmlSpecificationCase case1 = M.JmlSpecificationCase(null, false, null, null, lhs, null);
        JmlSpecificationCase case2 = M.JmlSpecificationCase(null, false, null, null, rhs, null);
        
        JmlMethodClauseGroup group = M.JmlMethodClauseGroup(List.of(case1, case2));
        
        if(clauses==null){
            return List.of((JmlMethodClause)group);
        }
        
        return clauses.append(group);
        
        
    }
     
    public Map<Prop,String> freeze(Map<Prop,String> m){
        m = p1.freeze(m);
        m = p2.freeze(m);
        
        return m;
    }

    
    public JCExpression toTree(JmlTreeUtils treeutils){
        return treeutils.makeBinary(0, JCTree.Tag.OR, p1.toTree(treeutils), p2.toTree(treeutils));
    }
    
    
    
    @Override
    public void accept(IPropElementVisitor visitor) {        
        visitor.visitOr(this);
    }
    
}
