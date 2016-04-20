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
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
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

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

public class Strongarm {

    final protected Context                context;

    private final static String            separator = "---------------------";

    final protected Log                    log;

    final protected Utils                  utils;

    final protected JmlInferPostConditions infer;

    final protected JmlTreeUtils           treeutils;

    public Strongarm(JmlInferPostConditions infer) {
        this.infer = infer;
        this.context = infer.context;
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
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
        
        if (printContracts) {
            log.noticeWriter.println("--------------------------------------"); 
            log.noticeWriter.println("INFERRED POSTCONDITION OF " + utils.qualifiedMethodSig(methodDecl.sym)); 
            log.noticeWriter.println(JmlPretty.write(contract));
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
        
        sp(blockIndex, program.blocks());
        
        return null;
    }
    public boolean skip(JCStatement stmt){
      
        // we only care about assignments (assumes)
        if(stmt instanceof JmlStatementExpr && ((JmlStatementExpr)stmt).label == Label.ASSIGNMENT){
            JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;

            // we only care about assignments
            if(!(jmlStmt.expression instanceof JCBinary && ((JCBinary)jmlStmt.expression).lhs instanceof JCIdent)){
                return true;
            }

            // we don't care about the internal JML stuff (unless it's the result!)
            if(((JCIdent)((JCBinary)jmlStmt.expression).lhs).getName().toString().startsWith("_JML___") && 
                    !((JCIdent)((JCBinary)jmlStmt.expression).lhs).getName().toString().startsWith("_JML___result")){
                return true;
            }
        
        
            return false;
        }
            
        return true;
    }
    public Prop<JCBinary> sp(Map<String,Integer> idx, List<BasicBlock> blocks){
        // find the precondition in the first block
        boolean verbose        = infer.verbose;

        Prop<JCBinary> precondition = null;
        BasicBlock startBlock = null;
        
        
        for(int b=0; b < blocks.size() && precondition==null; b++){
            
            startBlock = blocks.get(b);
            
            for(JCStatement stmt : startBlock.statements()){
                if(skip(stmt)){ continue; }
                
                JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;
                
                if(jmlStmt.label == Label.PRECONDITION){
                    precondition = new Prop<JCBinary>((JCBinary)jmlStmt.expression);
                }
            }    
        }
        
        if(precondition==null){
            if (verbose) {
                log.noticeWriter.println("Couldn't locate the precondition in any of the basic blocks. Will assume true for the precondition.");
            }
            //JCBinary jcBinary;
        }
        
        if(startBlock==null){
            if (verbose) {
                log.error("jml.internal", "Failed to find any starting blocks... Cannot infer contracts"); 
            }            
        }

        //
        // begin execution
        //
        return sp(precondition, idx, blocks, startBlock.followers().get(0));
    }
    public Prop<JCBinary> sp(Prop<JCBinary> p, Map<String,Integer> idx, List<BasicBlock> blocks, BasicBlock block){
        return null;
    }
}
