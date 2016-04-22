package org.jmlspecs.openjml.strongarm;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.BasicBlocker2;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.strongarm.transforms.RemoveTautologies;
import org.jmlspecs.openjml.strongarm.transforms.SubstituteTree;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCUnary;
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
    
    final protected static com.sun.tools.javac.util.List JDKList = com.sun.tools.javac.util.List.of(null);
    
    public Strongarm(JmlInferPostConditions infer) {
        this.infer = infer;
        this.context = infer.context;
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.M = JmlTree.Maker.instance(context);
        
        // cache a copy of the replacement util
        {
            new SubstituteTree(context);
            new RemoveTautologies(context);
        }
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
        
        if (verbose) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------"); 
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("BEFORE FINAL TRANSFORMATION OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            log.noticeWriter.println(JmlPretty.write(contract));
        }
        
        ///
        /// Perform cleanup
        ///
        {
            cleanupContract(methodDecl, contract);
        }
        ///
        ///
        ///
        
        
        ///
        /// Put the contracts back together 
        ///
        JmlMethodClause newCase = M.JmlMethodClauseExpr(JmlToken.ENSURES, (JCExpression)contract);
                
        if(methodDecl.cases!=null){ // if we already have specification cases, add this
            methodDecl.cases.cases.head.clauses = methodDecl.cases.cases.head.clauses.appendList(com.sun.tools.javac.util.List.of(newCase));
        }else{                      // otherwise create a new one (with a "true" precondition)

            if(JmlOption.isOption(context, JmlOption.INFER_DEFAULT_PRECONDITIONS)){
                // create the default precondition 
                JmlMethodClauseExpr defaultPrecondition = M.JmlMethodClauseExpr
                        (
                                JmlToken.REQUIRES,  
                                treeutils.makeBinary(0, JCTree.EQ, treeutils.trueLit, treeutils.trueLit)
                        );
                
                JmlSpecificationCase cases = M.JmlSpecificationCase(null, false, null, null, JDKList.of(defaultPrecondition, newCase));
    
                methodDecl.cases = M.JmlMethodSpecs(JDKList.of(cases));
                methodDecl.cases.decl = methodDecl;
                methodDecl.methodSpecsCombined = new MethodSpecs(null, methodDecl.cases);
            }else{
                if (verbose) {
                    log.noticeWriter.println(Strings.empty);
                    log.noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
                    log.noticeWriter.println(Strings.empty);
                    log.noticeWriter.println("MISSING PRECONDITION OF " + utils.qualifiedMethodSig(methodDecl.sym) + "... (SKIPPING)"); //$NON-NLS-1$
                    log.noticeWriter.println("(hint: enable -infer-default-preconditions to assume a precondition)");
                }
            }
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
               
        Prop<JCExpression> props = sp(program.blocks());
        
        if (verbose) {
            log.noticeWriter.println("Inference finished...");
        }
        
        if (verbose) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------"); 
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("FINISHED (STAGE 1) INFERENCE OF " + utils.qualifiedMethodSig(methodDecl.sym)); 
            log.noticeWriter.println(JmlPretty.write(methodDecl));
        }
        
        List<JCTree> subs = new ArrayList<JCTree>(); extractSubstitutions(program.blocks().get(0), subs);
        // First, perform the substitutions
        
        // backwards!
        ListIterator<JCTree> it = subs.listIterator(subs.size());
        
        while(it.hasPrevious()){
            JCTree t = it.previous();

            log.noticeWriter.println("--------------------------------------");
            log.noticeWriter.println("wanting to replace: " + t.toString());
            props.replace(t);
            log.noticeWriter.println("--------------------------------------"); 
        }
        
        // Second, remove locals, and apply some techniques to make things more readable.
        
        
        if (verbose) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------"); 
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("FINISHED (STAGE 2) INFERENCE OF " + utils.qualifiedMethodSig(methodDecl.sym)); 
            log.noticeWriter.println(JmlPretty.write(methodDecl));
        }

        
        
        // Convert this into a JCTree
        return props.toTree(treeutils);
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
        if(stmt.label == Label.ASSIGNMENT){
            return true;
        }
        return false;
    }
    
    public Prop<JCExpression> sp(List<BasicBlock> blocks){
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
        // normal execution skips the bodyBegin block
        if(startBlock.followers().get(0).id().getName().toString().contains("bodyBegin")){
            return sp(precondition, blocks, startBlock.followers().get(0).followers().get(0));            
        }
        
        return sp(precondition, blocks, startBlock.followers().get(0));
    }
    public Prop<JCExpression> sp(Prop<JCExpression> p, List<BasicBlock> blocks, BasicBlock block){
        boolean verbose        = infer.verbose;

        if(skipBlock(block)){
            return p;
        }
        
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
                    sp(p, blocks, block.followers().get(0)), 
                    sp(p, blocks, block.followers().get(1))
                    );
            
        }else if(block.followers().size() == 1){
            return  sp(p, blocks, block.followers().get(0));
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
    
    public void cleanupContract(JmlMethodDecl methodDecl, JCTree contract){
        boolean verbose        = infer.verbose;

        //
        // Perform logical simplification
        //
        RemoveTautologies.simplify(contract);

        if (verbose) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------"); 
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("AFTER REMOVING TAUTOLOGIES OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            log.noticeWriter.println(JmlPretty.write(contract));
        }
        
        //
        // Remove local variables
        //

        
        if (verbose) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("AFTER REMOVING LOCALS OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            log.noticeWriter.println(JmlPretty.write(contract));
        }
        
        //
        // Simplify labels
        //
        
        if (verbose) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("AFTER SIMPLIFYING LABELS OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            log.noticeWriter.println(JmlPretty.write(contract));
        }
        
    }
}
