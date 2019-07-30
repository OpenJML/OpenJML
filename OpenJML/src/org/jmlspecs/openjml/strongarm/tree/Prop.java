package org.jmlspecs.openjml.strongarm.tree;


import sun.misc.Unsafe;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.ext.MethodExprClauseExtensions;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.RecommendsClause.*;
import static org.jmlspecs.openjml.ext.AssignableClauseExtension.*;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.strongarm.AnalysisTypes;
import org.jmlspecs.openjml.strongarm.AnalysisTypes.AnalysisType;
import org.jmlspecs.openjml.strongarm.BlockReader;
import org.jmlspecs.openjml.strongarm.InferenceAbortedException;
import org.jmlspecs.openjml.strongarm.Strongarm;
import org.jmlspecs.openjml.strongarm.transforms.CleanupPrestateAssignable;
import org.jmlspecs.openjml.strongarm.transforms.SubstituteTree;
import org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2;
import org.jmlspecs.openjml.vistors.JmlTreeCopier;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;

public class Prop<T extends JCExpression> implements Cloneable, IPropElement {

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
        //this.p = JmlTreeCopier.copy(Strongarm.MM, (T)p.clone());
        this.p = JmlTreeCopier.copy(Strongarm.MM, p);
        
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
            log.getWriter(WriterKind.NOTICE).println(String.format("[INFER] [%s] %s", Strongarm.Current, msg));
        }
    }
    
    public void logl(String msg){
        if(verbose){
            log.getWriter(WriterKind.NOTICE).println(String.format("[INFER] [%s] %s", Strongarm.Current, msg));
        }
    }
    
    public void replace(ArrayList<JCTree> subs) throws InferenceAbortedException{
        
        Strongarm.dieIfNeeded();
        
        JCExpression e = null;
        
        if(def==null){
            log("[SUBS] Skipping synthetic precondition (nothing to substitute)");
            return;
        }

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
   
    public void replace(Map<JCIdent, ArrayList<JCTree>> mappings, boolean limitDepth) throws InferenceAbortedException{
        
        Strongarm.dieIfNeeded();
        
        replace2(mappings, limitDepth);   
    }
    
    public void replace3(Map<JCIdent, ArrayList<JCTree>> mappings, boolean limitDepth) throws InferenceAbortedException{
        
        Strongarm.dieIfNeeded();
        
        if(def==null){
            log("[SUBS] Skipping synthetic precondition (nothing to substitute)");
            return;
        }

        
        log("[SUBS ] Running Substitution For Expression: " + p.toString() + ", Defined @ Block: " + def.id().toString());
        log("[DEBUG] ADDR PROP=" + Integer.toHexString(System.identityHashCode(this)) + ", EXPR=" + Integer.toHexString(System.identityHashCode(p)));        
        
        //
        // Print path
        //
//        logl("[PATH]");        
//        
//        for(BasicBlock b : path){
//            logl(b.id().toString() + ">>");
//        }
//        
//        if(p.toString().contains("b_207")){
//            System.out.println("");
//        }
        
        String beforeFixpoint = p.toString();
        
        //
        // a) baby fix point
        //
        String before;
        int iteration = 1;
        
        //
        // b) 
        //
        do {
            Strongarm.dieIfNeeded();
            log("\tInternal Fixpoint #" + iteration);

            before = p.toString();

            log("\t\tBefore: " + before);
            doReplacement3();
            log("\t\tAfter: " + p.toString());
            
            
            iteration++;
            
        }while(before.equals(p.toString())==false);

        
        String afterFixpoint = p.toString();
      
    }

    public void replace2(Map<JCIdent, ArrayList<JCTree>> mappings, boolean limitDepth) throws InferenceAbortedException{
        
        Strongarm.dieIfNeeded();
        
        if(mappings!=null){
            replace1(mappings, limitDepth);
            return;
        }
        
        if(limitDepth==false){
            replace3(mappings, limitDepth);
            return;
        }

        if(def==null){
            log("[SUBS] Skipping synthetic precondition (nothing to substitute)");
            return;
        }
        log("[SUBS] Running Substitution For Expression: " + p.toString() + ", Defined @ Block: " + def.id().toString());
        log("[DEBUG] ADDR PROP=" + Integer.toHexString(System.identityHashCode(this)) + ", EXPR=" + Integer.toHexString(System.identityHashCode(p)));
        // print path
//        logl("[PATH]");        
//        for(BasicBlock b : path){
//            logl(b.id().toString() + ">>");
//        }
//        
                // baby fixpoint
        String before;
        int iteration = 1;
        
        
                
        do {
            Strongarm.dieIfNeeded();
            
            log("\tInternal Fixpoint #" + iteration);

            before = p.toString();

            log("\t\tBefore: " + before);
            doReplacement2();
            log("\t\tAfter: " + p.toString());
            
            
            iteration++;
            
        }while(before.equals(p.toString())==false);
        
    }
    
    private void doReplacement2() throws InferenceAbortedException{
        
        Strongarm.dieIfNeeded();
        
        JCExpression tmpE = null;
        
        if(p instanceof JCBinary){

            JCBinary b = (JCBinary)p;
            
            // replacements only need to happen on the RHS of an expression if 
            // it's an assignment 
            if(label == Label.ASSIGNMENT){
                tmpE = SubstituteTree2.replace(BlockReader._substitutionCache, path, b.rhs, false); 
                
                if(tmpE!=null){
                   b.rhs = (T) tmpE;
                   
                   if(SubstituteTree2.instance.currentReplacement instanceof JCBinary){
                       JCBinary theReplacement = (JCBinary)SubstituteTree2.instance.currentReplacement;
                       if(theReplacement.lhs instanceof JCIdent && theReplacement.lhs.toString().startsWith("_JML__tmp")){
                           // make sure the operators match
                           if(b.operator.toString().startsWith("==")==false){
                               b.operator = theReplacement.operator;
                               b.opcode   = theReplacement.opcode;
                           }
                       }
                   }
                }
            }else{
                tmpE = SubstituteTree2.replace(BlockReader._substitutionCache, path, p, false);  
                
                if(tmpE!=null){
                    p = (T) tmpE;
                }
            }
            
        }else{
             tmpE = SubstituteTree2.replace(BlockReader._substitutionCache, path, p, false);
             
             if(tmpE!=null){
                 p = (T) tmpE;
             }
        }
        
       
        
    }
    

    
    private void doReplacement3() throws InferenceAbortedException{
        
        Strongarm.dieIfNeeded();
        
        JCExpression tmpE = null;
        
        if(p instanceof JCBinary){

            JCBinary b = (JCBinary)p;
            
            tmpE = SubstituteTree2.replace(BlockReader._premapCache, path, p);  
            
            if(tmpE!=null){
                p = (T) tmpE;
            }
            
            // replacements only need to happen on the RHS of an expression if 
            // it's an assignment 
//            if(label == Label.ASSIGNMENT){
//                tmpE = SubstituteTree2.replace(BlockReader._premapCache, path, b.rhs); 
//                
//                if(tmpE!=null){
//                   b.rhs = (T) tmpE;
//                }
//            }else{
//                tmpE = SubstituteTree2.replace(BlockReader._premapCache, path, p);  
//                
//                if(tmpE!=null){
//                    p = (T) tmpE;
//                }
//            }
            
        }else{
             tmpE = SubstituteTree2.replace(BlockReader._premapCache, path, p);
             
             if(tmpE!=null){
                 p = (T) tmpE;
             }
        }        
    }
    

    
    public void replace1(Map<JCIdent, ArrayList<JCTree>> mappings, boolean limitDepth) throws InferenceAbortedException{
        
        Strongarm.dieIfNeeded();
        
        if(def==null){
            return;
        }
        
        if(!Strongarm.freezer.containsKey(this) || !p.toString().equals(Strongarm.freezer.get(this))){
            log("[SUBS PASS 2] SKIPPING Substitution For Expression: " + p.toString() + ", Defined @ Block: " + def.id().toString());
            return;
        }
        
        log("[SUBS PASS 2] Substitution For Expression: " + p.toString() + ", Defined @ Block: " + def.id().toString());
        
        log("[DEBUG] ADDR PROP=" + Integer.toHexString(System.identityHashCode(this)) + ", EXPR=" + Integer.toHexString(System.identityHashCode(p)));
        // print path
//        logl("[PATH]");        
//        for(BasicBlock b : path){
//            logl(b.id().toString() + ">>");
//        }
//        log("");
//        
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
    
    private void doReplacement(ArrayList<JCTree> subs) throws InferenceAbortedException{
        
        Strongarm.dieIfNeeded();
        
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
                    MethodExprClauseExtensions.ensuresID,  
                    MethodExprClauseExtensions.ensuresClauseKind,  
                    p
            );

            // did we modify something? if so, let's add that badboy right here.
            if(label==null && p instanceof JCBinary && AnalysisTypes.enabled(AnalysisType.FRAMES)){
                
                JCBinary jmlBinary = (JCBinary)p;
                
                // it's some kind of assignment
                if(jmlBinary.operator.toString().startsWith("==")){
                    
                    
                    if(jmlBinary.lhs instanceof JmlBBArrayAccess){
                        // TODO -- add * permission
                    }
                    
                    return List.of(
                            clause,
                            M.JmlMethodClauseStoreRef(assignableID, assignableClauseKind, List.of(jmlBinary.lhs))
                            );
                }
                
            }
            
        }else{
            clause = M.JmlMethodClauseExpr
            (
                    requiresID,  
                    requiresClauseKind,  
                    p
            );

        }

        return List.of((JmlMethodClause)clause);
    }
    
    public JCExpression toTree(JmlTreeUtils treeutils){
        return p;
    }
    
    
    // # f = a & (b | (c & d))
    public String toPyEDA(EDAConverter map){
        
        String s = p.toString();
        
        return map.get(s);
        
    }
    
    
    public boolean isBranchStmt(){
        if(label == Label.BRANCHT || label == Label.BRANCHE || label == Label.BRANCHC || label == Label.CASECONDITION){
            return true;
        }

        return false;
    }

    public Map<Prop,String> freeze(Map<Prop,String> m){
        m.put(this,  p.toString());        
        return m;
    }
    
    
    public static int count = 0;
    @Override 
    public Object clone(){
                
        //count++;
        
        // this method automatically does a deep copy. 
        Prop<T> clonedProp = new Prop<T>(p, def, label);
        
        clonedProp.path = path;
        
        //System.out.println("$$COUNT: " + count);
         
        return clonedProp;
         
    }

    @Override
    public void accept(IPropElementVisitor visitor) {
        visitor.visitProp(this);
    }
}

