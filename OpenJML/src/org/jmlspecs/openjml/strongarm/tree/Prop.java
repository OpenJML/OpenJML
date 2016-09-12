package org.jmlspecs.openjml.strongarm.tree;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Map;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
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
    public Label label;
    
    public Prop(T p, BasicBlock def){
        this.p = p;
        this.def = def;
    }
    
    public Prop(T p, BasicBlock def, Label label){
        this.p = p;
        this.def = def;
        this.label = label;
    }

    public Prop(){}
    
    public void replace(ArrayList<JCTree> subs){
        
        JCExpression e = null;
        
        System.out.println("Running Substitution For Expression: " + p.toString() + ", Defined @ Block: " + def.id().toString());
        // build a list of substitutions by following the mapping backwards.
        
        if(p.toString().contains("_JML___NEWARRAY_317")){
            System.out.println("Found failing prop...");
        }
        
        
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
    
    
    public void replace(Map<JCIdent, ArrayList<JCTree>> mappings, boolean limitDepth){
        
                
        System.out.println("Running Substitution For Expression: " + p.toString() + ", Defined @ Block: " + def.id().toString());
        // build a list of substitutions by following the mapping backwards.
        
        if(p.toString().contains("_JML___result_98_477___41")){
            System.out.println("Found failing prop...");
        }
        
        ArrayList<JCTree> subs = new ArrayList<JCTree>(); //getSubstitutionTree(def, new ArrayList<JCTree>(), mappings);
        
        if(!limitDepth){
           subs = getSubstitutionTree(def, new ArrayList<JCTree>(), mappings);
        }else{
          
            if(mappings.get(def.id())!=null){
              subs.addAll(mappings.get(def.id()));
            }

        }
        
        //
        Collections.reverse(subs);
        //
        
        // baby fixpoint
        String before;
        int iteration = 1;
                
        do {
            System.out.println("Internal Fixpoint #" + iteration);

            before = p.toString();
            
            doReplacement(subs);
            
            
            iteration++;
            
        }while(before.equals(p.toString())==false && limitDepth==false);
        
    }
    
    private void doReplacement(ArrayList<JCTree> subs){
        
        JCExpression e = null;

        for(JCTree sub : subs){
             
            if(sub.toString().contains("ASSERT_52_207_207___24")){
                 System.out.println("Found failing prop...");
             }
            /* if(sub.toString().startsWith("tricky_228")){
                 System.out.println("Found failing prop...");
             }
             */
            //System.out.println("Trying: " + sub.toString());
            
            JCExpression tmpE;
            
             if(e!=null){
                 tmpE = SubstituteTree.replace(sub, e);
             }else{
                 tmpE = SubstituteTree.replace(sub,  p);
             }
             
             if(tmpE!=null){
                 e = tmpE;
             }
             
         }
         
         if(e!=null){
             p = (T) e;
         }
        
    }
    
    public ArrayList<JCTree> getSubstitutionTree(BasicBlock b, ArrayList<JCTree> subs, Map<JCIdent, ArrayList<JCTree>> mappings){
        
        if(b==null){ return subs; }
        
        //System.out.println("Getting Substitutions from Block: " + b.id().toString());

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
        
        //TODO 
        if(p.toString().contains(Strings.resultVarString) || !isBranchStmt()){
            clause = M.JmlMethodClauseExpr
            (
                    JmlToken.ENSURES,  
                    p
            );

            // did we modify something? if so, let's add that badboy right here.
            if(label==null && p instanceof JCBinary){
                
                JCBinary jmlBinary = (JCBinary)p;
                
                // it's some kind of assignment
                if(jmlBinary.operator.toString().startsWith("==")){
                    
                    
                    if(jmlBinary.lhs instanceof JmlBBArrayAccess){
                        // TODO -- add * permission
                    }
                    
                    return List.of(
                            clause,
                            M.JmlMethodClauseStoreRef(JmlToken.ASSIGNABLE, List.of(jmlBinary.lhs))
                            );
                }
                
            }
            
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
    
    
    public boolean isBranchStmt(){
        if(label == Label.BRANCHT || label == Label.BRANCHE || label == Label.BRANCHC || label == Label.CASECONDITION){
            return true;
        }

        return false;
    }
}

