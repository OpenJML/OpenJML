package org.jmlspecs.openjml.strongarm.tree;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Map;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.strongarm.JDKListUtils;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.List;

public class Or<T extends JCExpression> extends Prop<T> {

    public Prop<T> p1;
    public Prop<T> p2;
    
    public Or(Prop<T> p1, Prop<T> p2){
        this.p1 = p1;
        this.p2 = p2;
    }
    
    public void replace(Map<JCIdent, ArrayList<JCTree>> mappings){
        p1.replace(mappings);
        p2.replace(mappings);
    }
    
    public void replace(ArrayList<JCTree> mappings){
        p1.replace(mappings);
        p2.replace(mappings);        
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
        
        JmlSpecificationCase case1 = M.JmlSpecificationCase(null, false, null, null, lhs);
        JmlSpecificationCase case2 = M.JmlSpecificationCase(null, false, null, null, rhs);
        
        JmlMethodClauseGroup group = M.JmlMethodClauseGroup(List.of(case1, case2));
        
        if(clauses==null){
            return List.of((JmlMethodClause)group);
        }
        
        return clauses.append(group);
        
        
    }
     
    public JCExpression toTree(JmlTreeUtils treeutils){
        return treeutils.makeBinary(0, JCTree.OR, p1.toTree(treeutils), p2.toTree(treeutils));
    }
    
    class ContractComparator implements Comparator<JmlMethodClause> {

        // ordering is requires, ensures, modifies (otherwise lexical)
        @Override
        public int compare(JmlMethodClause o1, JmlMethodClause o2) {
            
            if(o1.token == o2.token){
                return 0;
            }
            
            if(o1.token == JmlToken.REQUIRES && o2.token == JmlToken.ENSURES){
                return -1;
            }
            
            if(o2.token == JmlToken.REQUIRES && o1.token == JmlToken.ENSURES){
                return 1;
            }
            
            return o2.token.toString().compareTo(o1.token.toString());
        }
        
    }
    
}
