package org.jmlspecs.openjml.strongarm;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.List;

public class Or<T extends JCExpression> extends Prop<T> {

    public Prop<T> p1;
    public Prop<T> p2;
    
    public Or(Prop<T> p1, Prop<T> p2){
        this.p1 = p1;
        this.p2 = p2;
    }
    
    public void replace(JCTree replacement){
        p1.replace(replacement);
        p2.replace(replacement);
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

        JmlSpecificationCase case1 = M.JmlSpecificationCase(null, false, null, null, lhs);
        JmlSpecificationCase case2 = M.JmlSpecificationCase(null, false, null, null, rhs);
        
        JmlMethodClauseGroup group = M.JmlMethodClauseGroup(List.of(case1, case2));
        
       return clauses.append(group);
    }
     
    public JCExpression toTree(JmlTreeUtils treeutils){
        return treeutils.makeBinary(0, JCTree.OR, p1.toTree(treeutils), p2.toTree(treeutils));
    }
    
    
}
