package org.jmlspecs.openjml.strongarm;

import java.util.ArrayList;
import java.util.Map;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
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
    public BasicBlock def;
    
    public Prop(T p, BasicBlock def){
        this.p = p;
        this.def = def;
    }
    
    public Prop(){}
    
    public void replace(Map<JCIdent, ArrayList<JCTree>> mappings){
        
        JCExpression e = null;
        
        
        System.out.println("Running Substitution For Expression: " + p.toString() + ", Defined @ Block: " + def.id().toString());
        // build a list of substitutions by following the mapping backwards.
        
        ArrayList<JCTree> subs = getSubstitutionTree(def, new ArrayList<JCTree>(), mappings);
        
        for(JCTree sub : subs){
            if(e!=null){
                e = SubstituteTree.replace(sub, e);
            }else{
                e = SubstituteTree.replace(sub,  p);
            }
        }
        
        if(e!=null){
            p = (T) e;
        }
    }
    
    public ArrayList<JCTree> getSubstitutionTree(BasicBlock b, ArrayList<JCTree> subs, Map<JCIdent, ArrayList<JCTree>> mappings){
        
        if(b==null){ return subs; }
        
        System.out.println("Getting Substitutions from Block: " + b.id().toString());

        if(mappings.get(b.id())!=null){
            subs.addAll(mappings.get(b.id()));
        }

        for(BasicBlock before : b.preceders()){
            getSubstitutionTree(before, subs, mappings);
        }
        
        return subs;
    }
    
    public List<JmlMethodClause> getClauses(List<JmlMethodClause> clauses, JmlTreeUtils treeutils, JmlTree.Maker M){
        
        JmlMethodClauseExpr clause; 
        
        //TODO correctly detect this.
        if(p.toString().contains("_JML___result")){
            clause = M.JmlMethodClauseExpr
            (
                    JmlToken.ENSURES,  
                    p
            );

        }else{
            clause = M.JmlMethodClauseExpr
            (
                    JmlToken.REQUIRES,  
                    p
            );

        }

        return List.of((JmlMethodClause)clause);
    }
    
    public JCExpression toTree(JmlTreeUtils treeutils){
        return p;
    }
    
}

