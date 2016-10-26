package org.jmlspecs.openjml.strongarm.tree;


import sun.misc.Unsafe;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Map;
import java.util.Stack;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.strongarm.Strongarm;
import org.jmlspecs.openjml.strongarm.transforms.CleanupPrestateAssignable;
import org.jmlspecs.openjml.strongarm.transforms.SubstituteTree;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

public class Prop<T extends JCExpression> implements Cloneable {

    public T p;
    public BasicBlock def;
    public Label label;
    public ArrayList<BasicBlock> path;
    
    ///
    ///
    final protected Log                    log;
    final protected Utils                  utils;
    public static boolean verbose = false; 

    
    public Prop(T p, BasicBlock def){
        this.p = p;
        this.def = def;
        
        this.log = Log.instance(Strongarm._context);
        this.utils = Utils.instance(Strongarm._context);
        
        
        init();
    }
    
    public void init(){
        this.verbose = JmlOption.isOption(Strongarm._context,"-verbose") // The Java verbose option
                || utils.jmlverbose >= Utils.JMLVERBOSE;
        
    }
    
    public Prop(T p, BasicBlock def, Label label){
        this.p = JmlTreeCopier.copy(Strongarm.MM, (T)p.clone());
        this.def = def;
        this.label = label;
        
        this.log = Log.instance(Strongarm._context);
        this.utils = Utils.instance(Strongarm._context);
        
        
        init();
    }

    public Prop<T> fix(Stack<BasicBlock> p){
        path = new ArrayList<BasicBlock>();
        
        path.addAll(p);
        
        return this;
    }
    
    public Prop(){
        
        this.log = Log.instance(Strongarm._context);
        this.utils = Utils.instance(Strongarm._context);
        
        
        init();
        
    }
    
    public void log(String msg){
        if(verbose){
            log.noticeWriter.println(msg);
        }
    }
    
    public void logl(String msg){
        if(verbose){
            log.noticeWriter.print(msg);
        }
    }
    
    public void replace(ArrayList<JCTree> subs){
        
        JCExpression e = null;
        
        log("Running Substitution For Expression: " + p.toString() + ", Defined @ Block: " + def.id().toString());
        // build a list of substitutions by following the mapping backwards.
        
        if(p.toString().contains("_JML___NEWARRAY_317")){
            log("Found failing prop...");
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
        
                
        log("[SUBS] Running Substitution For Expression: " + p.toString() + ", Defined @ Block: " + def.id().toString());
        log("[DEBUG] ADDR PROP=" + Integer.toHexString(System.identityHashCode(this)) + ", EXPR=" + Integer.toHexString(System.identityHashCode(p)));
        // print path
        logl("[PATH]");        
        for(BasicBlock b : path){
            logl(b.id().toString() + ">>");
        }
        log("");
        
        // build a list of substitutions by following the mapping backwards.
        
        if(def.id().toString().equals("BL_423_else_19")){
            log("");
        }
        
        if(p.toString().contains("_JML___result_400_467___9 == c_425_451___8")){
            log("Found failing prop...");
        }
        
        ArrayList<JCTree> subs = new ArrayList<JCTree>(); //getSubstitutionTree(def, new ArrayList<JCTree>(), mappings);
        
        
        subs = getSubstitutionTree(def, new ArrayList<JCTree>(), mappings, limitDepth);
        
        //
        Collections.reverse(subs);
        //
        
        subs.remove(p); // have to remove this or we get crazy results
        
        ArrayList<JCTree> removals = new ArrayList<JCTree>();
        
        for(JCTree t : subs){
            if(t.toString().equals(p.toString())){
                removals.add(t);
            }
        }
        
        subs.removeAll(removals);

        
//        for(JCTree ss : subs){
//            log("\t[SUB TABLE] " + ss.toString());
//        }
        
        // baby fixpoint
        String before;
        int iteration = 1;
                
        do {
            log("\tInternal Fixpoint #" + iteration);

            before = p.toString();

            log("\t\tBefore: " + before);
            doReplacement(subs);
            log("\t\tAfter: " + p.toString());
            
            
            iteration++;
            
        }while(before.equals(p.toString())==false);
        
    }
    
    private void doReplacement(ArrayList<JCTree> subs){
        
        JCExpression e = null;

        for(JCTree sub : subs){
             
            if(sub.toString().contains("THIS == THIS")){
                 //log("Found failing prop...");
                 continue;
             }
             
            //log("\t\t[ACTIVE SUB]" + sub.toString());
            
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
    
    public ArrayList<JCTree> getSubstitutionTree(BasicBlock b, ArrayList<JCTree> subs, Map<JCIdent, ArrayList<JCTree>> mappings, boolean limitDepth){
        
        if(b==null){ return subs; }
        
        //log("Getting Substitutions from Block: " + b.id().toString());

        if(mappings.get(b.id())!=null){
            subs.addAll(mappings.get(b.id()));
        }

        for(BasicBlock before : b.preceders()){
            // don't add substitutions that aren't in the path.
            if(limitDepth){
                if(path.contains(before) || before.id().toString().contains("bodyBegin") || before.id().toString().contains("Start")){
                    getSubstitutionTree(before, subs, mappings, limitDepth);
                }
            }else{
                getSubstitutionTree(before, subs, mappings, limitDepth);                
            }
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
    
    
    @Override 
    public Object clone(){
        
        // this method automatically does a deep copy. 
        Prop<T> clonedProp = new Prop<T>(p, def, label);
        
        clonedProp.path = path;
        
        return clonedProp;
        
    }
}

