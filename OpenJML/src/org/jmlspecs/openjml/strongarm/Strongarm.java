package org.jmlspecs.openjml.strongarm;

import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.esc.BasicBlocker2;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.esc.SMTTranslator;
import org.jmlspecs.openjml.esc.MethodProverSMT.SMTListener;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.SMT;

import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCLiteral;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

public class Strongarm {

    final protected Context                context;

    private final static String            separator = "---------------------";

    final protected Log                    log;

    final protected Utils                  utils;

    final protected JmlInferPostConditions infer;

    final protected JmlTreeUtils           treeutils;
    
    final protected JmlTree.Maker M;
    
    
    public Strongarm(JmlInferPostConditions infer) {
        this.infer = infer;
        this.context = infer.context;
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.M = JmlTree.Maker.instance(context);

    }

    public void infer(JmlMethodDecl methodDecl) {

        // first, we translate the method to the basic block format
        boolean printContracts = infer.printContracts;
        boolean verbose        = infer.verbose;

        JmlClassDecl currentClassDecl = utils.getOwner(methodDecl);

        JmlMethodSpecs denestedSpecs = methodDecl.sym == null ? null
                : JmlSpecs.instance(context).getDenestedSpecs(methodDecl.sym);

        // newblock is the translated version of the method body
        JmlMethodDecl translatedMethod = infer.assertionAdder.methodBiMap
                .getf(methodDecl);

        if (translatedMethod == null) {
            log.warning("jml.internal", "No translated method for "
                    + utils.qualifiedMethodSig(methodDecl.sym));
            return;
        }

        JCBlock newblock = translatedMethod.getBody();

        if (newblock == null) {
            log.error("esc.no.typechecking", methodDecl.name.toString()); //$NON-NLS-1$
            return;
        }

        if (verbose) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println(separator);
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("TRANSFORMATION OF " //$NON-NLS-1$
                    + utils.qualifiedMethodSig(methodDecl.sym));
            log.noticeWriter.println(JmlPretty.write(newblock));
        }

        BasicBlocker2 basicBlocker;

        BasicProgram program;

        basicBlocker = new BasicBlocker2(context);
        program = basicBlocker.convertMethodBody(
                newblock, 
                methodDecl,
                denestedSpecs, 
                currentClassDecl, 
                infer.assertionAdder);
        
        
        if (verbose) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println(separator);
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("BasicBlock2 FORM of "
                    + utils.qualifiedMethodSig(methodDecl.sym));
            log.noticeWriter.println(program.toString());
        }
        
        JCTree contract = infer(methodDecl, program);
        
        JmlSpecificationCase specCase = null;
        
        //methodDecl.cases.cases.append(methodDecl.cases.cases.get(0));
        //methodDecl.cases.cases;
        
        JmlMethodClause newCase = M.JmlMethodClauseExpr(JmlToken.ENSURES, (JCExpression)contract);
                
        if(methodDecl.cases!=null){
            
           
            JmlMethodClause[] clauses = new JmlMethodClause[methodDecl.cases.cases.head.clauses.size()+1];
            
            for(int i=0; i< methodDecl.cases.cases.head.clauses.size(); i++){
                clauses[i] = methodDecl.cases.cases.head.clauses.get(i);
            }
            clauses[clauses.length-1] = newCase;
            
            methodDecl.cases.cases.head.clauses = com.sun.tools.javac.util.List.from(clauses);
            
        }
        
        if (printContracts) {
            if(contract!=null){
                log.noticeWriter.println("--------------------------------------"); 
                log.noticeWriter.println("INFERRED POSTCONDITION OF " + utils.qualifiedMethodSig(methodDecl.sym)); 
                log.noticeWriter.println(JmlPretty.write(contract));
            }else{
                log.noticeWriter.println("--------------------------------------"); 
                log.noticeWriter.println("FAILED TO INFER THE POSTCONDITION OF " + utils.qualifiedMethodSig(methodDecl.sym)); 
            }
        }  
        
        // now, shove it back into the method
       
        if (verbose) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("FINISHED INFERENCE OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            log.noticeWriter.println(JmlPretty.write(methodDecl));
        }
        
    }
    /**
     * Entry point into the inference 
     * 
     * @param program
     * @return
     */
    public JCTree infer(JmlMethodDecl methodDecl, BasicProgram program){
        boolean printContracts = infer.printContracts;
        boolean verbose        = infer.verbose;

        
        // basic idea here is to boil it all down to a proposition. 
        // we take and solve / simplify that proposition and then translate it back into a 
        // post condition, which we then will add to the methodspecs. 
        
        // during the first pass we do no simplification
        
        if (verbose) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println(separator);
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("BasicBlock2 FORM of "
                    + utils.qualifiedMethodSig(methodDecl.sym));
            log.noticeWriter.println(program.toString());
        }
        
        // we are going to need to jump around the blocks, so build an index
        Map<String,Integer> blockIndex = new HashMap<String,Integer>();

        if (verbose) {
            log.noticeWriter.println("Building block index...");
        }

        for(int idx=0; idx < program.blocks().size(); idx++){
            blockIndex.put(program.blocks().get(idx).id().toString(), idx);
        }
        
        Prop<JCExpression> props = sp(blockIndex, program.blocks());
                
        //TODO - transform into a recognizable proposition
        
        // Convert this into a JCTree
        return props.toTree(treeutils);
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
            if(((JCIdent)((JCBinary)jmlStmt.expression).lhs).getName().toString().startsWith("_JML___result")){
                return false;
            }
        
            if(((JCIdent)((JCBinary)jmlStmt.expression).lhs).getName().toString().startsWith("_JML___")){ 
                return true;
            }

            if(((JCIdent)((JCBinary)jmlStmt.expression).lhs).getName().toString().startsWith("ASSERT_")){ 
                return true;
            }

        
            return false;
        }
        if(isBranchStmt(jmlStmt)){
            return false;
        }
        
        if(isPreconditionStmt(jmlStmt)){
            return false;
        }
            
        return true;
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
        if(stmt.label == Label.ASSIGNMENT){
            return true;
        }
        return false;
    }
    
    public Prop<JCExpression> sp(Map<String,Integer> idx, List<BasicBlock> blocks){
        // find the precondition in the first block
        boolean verbose        = infer.verbose;

        Prop<JCExpression> precondition = null;
        BasicBlock startBlock = null;
        
        
        for(int b=0; b < blocks.size() && precondition==null; b++){
            
            startBlock = blocks.get(b);
            
            for(JCStatement stmt : startBlock.statements()){
                if(skip(stmt)){ continue; }
                
                JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;
                
                if(isPreconditionStmt(jmlStmt)){
                    precondition = new Prop<JCExpression>((JCExpression)jmlStmt.expression);
                }
            }    
        }
        
        if(precondition==null){
            
            if (verbose) {
                log.noticeWriter.println("Couldn't locate the precondition in any of the basic blocks. Will assume true for the precondition.");
            }
            precondition = new Prop<JCExpression>(treeutils.makeBinary(0, JCTree.EQ, treeutils.trueLit, treeutils.trueLit));

            // reset the blocks
            startBlock = blocks.get(0);
        }
        
        if(startBlock==null){
            log.error("jml.internal", "Failed to find any starting blocks... Cannot infer contracts"); 
            return null; // TODO - do something else here? can we do something else?
        }

        //
        // begin execution
        //
        return sp(precondition, idx, blocks, startBlock.followers().get(0));
    }
    public Prop<JCExpression> sp(Prop<JCExpression> p, Map<String,Integer> idx, List<BasicBlock> blocks, BasicBlock block){
        boolean verbose        = infer.verbose;

        if (verbose) {
            log.noticeWriter.println("[STRONGARM] Inference at block " + block.id().toString());
        }
    
        
        for(JCStatement stmt : block.statements()){
        
            if(skip(stmt)){ continue; }
            
            JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;            
            
            p = And.of(p, new Prop<JCExpression>(jmlStmt.expression));            
        }
        
        // handle the if statement
        if(block.followers().size() == 2){
                        
            
            return Or.of(
                    sp(p, idx, blocks, block.followers().get(0)), 
                    sp(p, idx, blocks, block.followers().get(1))
                    );
        }else if(block.followers().size() == 1){
            return sp(p, idx, blocks, block.followers().get(0));
        }

        return p;
    }
}
