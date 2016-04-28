package org.jmlspecs.openjml.strongarm;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.strongarm.transforms.CleanupVariableNames;
import org.jmlspecs.openjml.strongarm.transforms.RemoveDuplicatePreconditions;
import org.jmlspecs.openjml.strongarm.transforms.RemoveDuplicatePreconditionsSMT;
import org.jmlspecs.openjml.strongarm.transforms.RemoveTautologies;
import org.jmlspecs.openjml.strongarm.transforms.SubstituteTree;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

public class BlockReader {
    
    final protected Context                context;

    final protected Log                    log;

    final protected Utils                  utils;

    final protected JmlTreeUtils           treeutils;
    
    final protected JmlTree.Maker M;
    
    final protected List<BasicBlock>       blocks;
    
    final protected boolean                verbose;
    
    final protected boolean                inferdebug;
    
    public Prop<JCExpression>             precondition;
    public Prop<JCExpression>             postcondition;
    
    private BasicBlock                     startBlock;
    
    public BlockReader(Context context, List<BasicBlock> blocks) {
        this.context = context;
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.blocks = blocks;
        
        this.inferdebug = JmlOption.isOption(context, JmlOption.INFER_DEBUG);           
        
        // verbose will print all the chatter
        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
        
    }
    public BasicBlock getStartBlock(){
        
        if(startBlock==null){pc(true);} // compute precondition
        
        return startBlock;
    }
    
    public Prop<JCExpression> pc(){
        return pc(false);
    }
    
    public Prop<JCExpression> pc(boolean recompute){

        if(precondition != null && recompute==false){
            return precondition;
        }
        
        for(int b=0; b < blocks.size() && precondition==null; b++){
            
            startBlock = blocks.get(b);
            
            for(JCStatement stmt : startBlock.statements()){
                if(skip(stmt)){ continue; }
                
                JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;
                
                if(isPreconditionStmt(jmlStmt)){
                    precondition = new Prop<JCExpression>((JCExpression)jmlStmt.expression, startBlock);
                }
            }     
        }
        
        if(precondition==null){
            
            if(JmlOption.isOption(context, JmlOption.INFER_DEFAULT_PRECONDITIONS)){
                if (verbose) {
                    log.noticeWriter.println("Couldn't locate the precondition in any of the basic blocks. Will assume true for the precondition.");
                }
                precondition = new Prop<JCExpression>(treeutils.makeBinary(0, JCTree.EQ, treeutils.trueLit, treeutils.trueLit), null);
    
                // reset the blocks
                startBlock = blocks.get(0);
            }else{                
                if (verbose) {
                    log.noticeWriter.println("Couldn't locate the precondition (and -infer-default-preconditions wasn't set)");
                }
                return null;
            }
        }
        
        return precondition;

    }
    
    public Prop<JCExpression> sp(){
        

        Prop<JCExpression> pre = pc();
        BasicBlock         start = getStartBlock();
        
        if(pre==null){
            return null;
        }
        
        if(startBlock==null){
            log.error("jml.internal", "Failed to find any starting blocks... Cannot infer contracts"); 
            return null; // TODO - do something else here? can we do something else?
        }

        //
        // begin execution
        //
        // normal execution skips the bodyBegin block
        if(startBlock.followers().get(0).id().getName().toString().contains("bodyBegin")){
            return sp(pre, startBlock.followers().get(0).followers().get(0));            
        }
        
        postcondition = sp(precondition, startBlock.followers().get(0));
        
        return postcondition;
    }
    private Prop<JCExpression> sp(Prop<JCExpression> p, BasicBlock block){

        if(skipBlock(block)){
            return p;
        }
        
        if (verbose) {
            log.noticeWriter.println("[STRONGARM] Inference at block " + block.id().toString());
        }    
        
        for(JCStatement stmt : block.statements()){        
            if(skip(stmt)){ continue; }
            
            JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;            
            
            p = And.of(p, new Prop<JCExpression>(jmlStmt.expression, block));            
        }
        
        // handle the if statement
        if(block.followers().size() == 2){

            return Or.of(
                    sp(p, block.followers().get(0)), 
                    sp(p, block.followers().get(1))
                    );
            
        }else if(block.followers().size() == 1){
            return  sp(p, block.followers().get(0));
        }

        return p;
    }
    
    public boolean skipBlock(BasicBlock block){
        String[] names = new String[]{"_return_", "tryTarget"};
        for(String name : names){
            if(block.id().getName().toString().contains(name)){
                return true;
            }
        }
        return false;
    }
    
    
    public boolean skip(JCStatement stmt){
      
        JmlStatementExpr jmlStmt;
        
        if(stmt instanceof JmlStatementExpr){
            jmlStmt = (JmlStatementExpr)stmt;
        }else{
            return true;
        }
        
        // we only care about assignments (assumes)
        if(isAssignStmt(jmlStmt)){
            
            // we only care about assignments
            if(!(jmlStmt.expression instanceof JCBinary && ((JCBinary)jmlStmt.expression).lhs instanceof JCIdent)){
                return true;
            }

            // we don't care about the internal JML stuff (unless it's the result!)
            if(((JCIdent)((JCBinary)jmlStmt.expression).lhs).getName().toString().startsWith(Strings.resultVarString)){
                return false;
            }
        
            if(((JCIdent)((JCBinary)jmlStmt.expression).lhs).getName().toString().startsWith("_JML___")){ 
                return true;
            }

            if(((JCIdent)((JCBinary)jmlStmt.expression).lhs).getName().toString().startsWith(Strings.assertPrefix)){ 
                return true;
            }

            if(((JCIdent)((JCBinary)jmlStmt.expression).lhs).getName().toString().contains("_heap__")){ 
                return true;
            }

            
            return false; //JCUnary
        }
        if(isBranchStmt(jmlStmt)){
            if(jmlStmt.expression instanceof JCBinary && ((JCIdent)((JCBinary)jmlStmt.expression).lhs).getName().toString().startsWith("_JML___")){
                return true;
            }
            
            if(jmlStmt.expression instanceof JCUnary){
            
                JCUnary unaryStmt = (JCUnary)jmlStmt.expression;
                
                if(unaryStmt.arg instanceof JCBinary){
                    if(((JCBinary)unaryStmt.arg).lhs.toString().startsWith("_JML___")){
                        return true;
                    }
                }
                
            }
            
            
            return false;
        }
        
        if(isPreconditionStmt(jmlStmt)){
            return false;
        }
            
        return true;
    }
    
    private boolean isVarDecl(JCStatement stmt){
        if(stmt instanceof JmlVariableDecl){
            return true;
        }
        return false;
    }
    
    private boolean isBranchStmt(JmlStatementExpr stmt){
        if(stmt.label == Label.BRANCHT || stmt.label == Label.BRANCHE){
            return true;
        }
        return false;
    }
    
    private boolean isPreconditionStmt(JmlStatementExpr stmt){
        if(stmt.label == Label.PRECONDITION){
            return true;
        }
        return false;
    }
    
    private boolean isAssignStmt(JmlStatementExpr stmt){
        if(stmt.label == Label.ASSIGNMENT || stmt.label==Label.DSA){
            return true;
        }
        return false;
    }

    public void addSubstitutionAtBlock(JCTree sub, Map<JCIdent, ArrayList<JCTree>> mappings, BasicBlock block){
        
        if(mappings.get(block.id())==null){
            mappings.put(block.id(), new ArrayList<JCTree>());
        }
        
        mappings.get(block.id()).add(sub);
    }
    

    public Map<JCIdent, ArrayList<JCTree>> getSubstitutionMappings(){
        
        Map<JCIdent, ArrayList<JCTree>> subs = getSubstitutionMappings(new HashMap<JCIdent, ArrayList<JCTree>>(), blocks.get(0));

        return subs;        
    }
    
    public Map<JCIdent, ArrayList<JCTree>> getSubstitutionMappings(Map<JCIdent, ArrayList<JCTree>> mappings, BasicBlock block){

        for(JCStatement stmt : block.statements()){

            if(stmt instanceof JmlStatementExpr){
                JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;
                
                if(isAssignStmt(jmlStmt)){
                    addSubstitutionAtBlock(jmlStmt.expression, mappings, block);
                }
            }else if(isVarDecl(stmt)){
                JmlVariableDecl decl = (JmlVariableDecl)stmt;
                addSubstitutionAtBlock(decl, mappings, block);
            }
        }
        
        if(block.followers().size()==2){
            getSubstitutionMappings(mappings, block.followers().get(0));
            getSubstitutionMappings(mappings, block.followers().get(1));
        }else if(block.followers().size()==1){
            getSubstitutionMappings(mappings, block.followers().get(0));
        }
        
        return mappings;
    }
    
    // types will be of either or a JCExpression thing or a JCVariableDecl thing -- either can be used for stitutions...
    public List<JCTree> extractSubstitutions(BasicBlock block, List<JCTree> subs){
       
        for(JCStatement stmt : block.statements()){

            if(stmt instanceof JmlStatementExpr){
                JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;
                
                if(isAssignStmt(jmlStmt)){
                    subs.add(jmlStmt.expression);
                }
            }else if(isVarDecl(stmt)){
                JmlVariableDecl decl = (JmlVariableDecl)stmt;
                subs.add(decl);
            }
        }
        
        if(block.followers().size()==2){
            extractSubstitutions(block.followers().get(0), subs);
            extractSubstitutions(block.followers().get(1), subs);
            
            
        }else if(block.followers().size()==1){
            extractSubstitutions(block.followers().get(0), subs);
        }
        
        return subs;
    }


}
