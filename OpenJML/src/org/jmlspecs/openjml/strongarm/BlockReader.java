package org.jmlspecs.openjml.strongarm;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;

import org.jmlspecs.openjml.JmlTree.JmlBBFieldAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.BasicBlocker2;
import org.jmlspecs.openjml.esc.BasicBlocker2.VarMap;
import org.jmlspecs.openjml.esc.BasicBlockerParent;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.strongarm.tree.And;
import org.jmlspecs.openjml.strongarm.tree.Or;
import org.jmlspecs.openjml.strongarm.tree.Prop;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.Symbol.VarSymbol;
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
    protected List<BasicBlock>       joins = new ArrayList<BasicBlock>();
    protected List<String>       preconditionAssertions = new ArrayList<String>();
    
    final protected boolean                verbose;
    
    final protected boolean                inferdebug;
    
    public Prop<JCExpression>             precondition;
    public Prop<JCExpression>             postcondition;
    
    private BasicBlock                     startBlock;
    private List<TraceElement> trace = new ArrayList<TraceElement>();
    private final BasicBlocker2 basicBlocker;
    private Map<JCIdent, ArrayList<JCTree>> _mappings;
    private boolean _mappingsDone;
    private Set<BasicBlock> exitBlocks;

    public BlockReader(Context context, List<BasicBlock> blocks, BasicBlocker2 basicBlocker) {
        this.context = context;
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.blocks = blocks;
        this.basicBlocker = basicBlocker;
        
        this.inferdebug = JmlOption.isOption(context, JmlOption.INFER_DEBUG);           
        
        // verbose will print all the chatter
        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
     
            init();
    }
    
    // compute some things we will need to do LCA analysis
    private void init(){
        
        // store all the join points in the CFG
        for(BasicBlock b : blocks){
            if(b.preceders().size() > 1){
                joins.add(b);
            }
        }
        // precondition assertions need to be removed so we need to store a mapping of which assertions (and variables) 
        // are the preconditions 
        for(BasicBlock b : blocks){
            for(JCStatement stmt : b.statements()){
                if(stmt instanceof JmlStatementExpr){
                    
                    JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;

                    if(jmlStmt.token == JmlToken.COMMENT && jmlStmt.toString().contains("Precondition")){
                        
                        // precondition?
                        String[] parts = jmlStmt.toString().split(":");
                        
                        if(parts.length == 2){
                            preconditionAssertions.add(parts[1].trim());
                            System.out.println("Added: " + parts[1].trim());
                        }
                    }
                }
                
            }
        }
        
    }
    public List<TraceElement> getTrace(){
        return trace;
    } 
    public BasicBlock getStartBlock(){
        
        if(startBlock==null){pc(true);} // compute precondition
        
        return startBlock;
    }
    
    public Prop<JCExpression> pc(){
        return pc(false);
    }
    
    private int depth = 0;
    
    public String getDepthStr(){
        StringBuffer buff = new StringBuffer();
        buff.append("|");
        buff.append(depth);
        buff.append("|");
        for(int i=0; i<depth; i++){
            buff.append("-");
        }
        return buff.toString();
    }
    public Prop<JCExpression> pc(boolean recompute){

        if(precondition != null && recompute==false){
            return precondition;
        }
        
        for(int b=0; b < blocks.size() && precondition==null; b++){
            
            startBlock = blocks.get(b);
            
            for(JCStatement stmt : startBlock.statements()){
                
                //if(skip(stmt)){ continue; }
                
                if(stmt instanceof JmlStatementExpr){
                    JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;
                    
                    if(isPreconditionStmt(jmlStmt)){
                        precondition = new Prop<JCExpression>((JCExpression)jmlStmt.expression, startBlock);
                    }
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
    
    private int loopDepth;
    
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
        
        initSp();
        
        postcondition = sp(precondition, startBlock.followers().get(0));
        
        
        return postcondition;
    }
    private Prop<JCExpression> sp(Prop<JCExpression> p, BasicBlock block){

        TraceElement traceElement = new TraceElement(block);
        
        if(skipBlock(block)){
            getExitBlocks().add(block);
            return p;
        }
        
        if (verbose) {
            log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "Inference at block " + block.id().toString());
        }    
        
        if(block.id().toString().contains(Constants.BL_LOOP_BODY)){              // activate loop processing. 
            loopDepth++;
        }else if(block.id().toString().contains(BasicBlockerParent.LOOPAFTER) || block.id().toString().contains(Constants.BL_LOOP_END)){ // deactivate 
            loopDepth--;
        }
        
        trace.add(traceElement);
        
        for(JCStatement stmt : block.statements()){
            
//            if(stmt.toString().contains("_JML___NEWARRAY_317_317.Array_length")){
//                System.out.println("");
//            }


            //
            // Used to pick up lexical mappings.
            //
            {
                pickupLexicalMappings(stmt, block);
            }
            
            if (verbose) {
                log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "STMT: " + stmt.toString());
            }    
            
            if(skip(stmt)){

                if (verbose) {
                    log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "ACTION: SKIP");
                }    

                continue; 
            }            

            JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;
                
            if(isPreconditionStmt(jmlStmt) || isPostconditionStmt(jmlStmt)){
                
                if (verbose) {
                    log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "ACTION: IGNORE PRE/POSTCONDITION ASSERTIONS/ASSUMES");
                }
                
                continue;
            }

            if (verbose) {
                log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "ACTION: PROCEED");
            }    

            if(verbose){
                log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "Accepting : " + jmlStmt.toString());
            }

            // fields get desugared into something else
            if(jmlStmt.expression instanceof JmlBBFieldAssignment){
                
                JmlBBFieldAssignment fieldAssignment = (JmlBBFieldAssignment)jmlStmt.expression;
                
                // assign OLD = RHS
                //JCExpression a1 = treeutils.makeBinary(0, JCTree.EQ, fieldAssignment.args.get(1), fieldAssignment.args.get(3));

                JmlBBFieldAccess access = new JmlBBFieldAccess((JCIdent)fieldAssignment.args.get(0), fieldAssignment.args.get(2));
                
                JCExpression a1 = treeutils.makeBinary(
                        0, 
                        JCTree.EQ, 
                        access, 
                        fieldAssignment.args.get(3)
                        );

                
                // assign NEW = OLD
                //JCExpression a2 = treeutils.makeBinary(0, JCTree.EQ, fieldAssignment.args.get(0), fieldAssignment.args.get(1));

                JCExpression a2 = treeutils.makeBinary(
                        0, 
                        JCTree.EQ, 
                        fieldAssignment.args.get(0), 
                        fieldAssignment.args.get(1)
                        );

                
                JmlStatementExpr e1 = treeutils.makeAssume(null, null, a1);
                //JmlStatementExpr e2 = treeutils.makeAssume(null, null, a2);
                

                p = And.of(p, new Prop<JCExpression>(e1.expression, block, e1.label));                
                traceElement.addExpr(e1.expression);

//                p = And.of(p, new Prop<JCExpression>(e2.expression, block));                
//                traceElement.addExpr(e2.expression);

                // add NEW == OLD
                VarMap blockMap  = basicBlocker.blockmaps.get(block);
                
                // add mapping for NEW -> OLD 
                //blockMap.putSAVersion(null, , 0);
                //blockMap.putSAVersion(vsym, version)
                if(fieldAssignment.args.get(0) instanceof JCIdent && fieldAssignment.args.get(1) instanceof JCIdent){
                    JCIdent o = (JCIdent)fieldAssignment.args.get(0);
                    JCIdent n = (JCIdent)fieldAssignment.args.get(1);

                    VarSymbol v = treeutils.makeVarSymbol(0, n.name, n.type, n.pos);
                    
                    blockMap.putSAVersion(v, o.name,1);
                }
                
                
            } else if(jmlStmt.expression instanceof JmlBBArrayAssignment){
              
                JmlBBArrayAssignment arrayAssignment = (JmlBBArrayAssignment)jmlStmt.expression;
                
                JmlBBArrayAccess arrayAccess = new JmlBBArrayAccess(
                        (JCIdent)arrayAssignment.args.get(0),
                        arrayAssignment.args.get(2),                        
                        arrayAssignment.args.get(3) 
                        );
                
                arrayAccess.type = arrayAssignment.args.get(0).type;
                
                JCExpression expr = treeutils.makeBinary(
                        0, 
                        JCTree.EQ, 
                        arrayAccess, 
                        arrayAssignment.args.get(4)
                        );
                
                
                JmlStatementExpr stmtExpr = treeutils.makeAssume(null, null, expr);

                p = And.of(p, new Prop<JCExpression>(stmtExpr.expression, block, stmtExpr.label));                
                traceElement.addExpr(stmtExpr.expression);


                // add NEW == OLD
                VarMap blockMap  = basicBlocker.blockmaps.get(block);
                
                // add mapping for NEW -> OLD 
//                if(fieldAssignment.args.get(0) instanceof JCIdent && fieldAssignment.args.get(1) instanceof JCIdent){
//                    JCIdent o = (JCIdent)fieldAssignment.args.get(0);
//                    JCIdent n = (JCIdent)fieldAssignment.args.get(1);
//
//                    VarSymbol v = treeutils.makeVarSymbol(0, n.name, n.type, n.pos);
//                    
//                    blockMap.putSAVersion(v, o.name,1);
//                }
//                

                
            } else{
                p = And.of(p, new Prop<JCExpression>(jmlStmt.expression, block, jmlStmt.label));                
                    
                traceElement.addExpr(jmlStmt.expression);
            }
            //
            // processing of symbolic execution substititions. 
            //
            
            
        }
        
        boolean ignoreBranch = ignoreBranch(block);

        //
        // this next bit handles turning off certain branches when processing loops.
        //
        {            
            if(loopDepth > 0 && block.followers().size() > 1){
         
                
                // ignore if we are in LoopBody
                if(block.id().toString().contains(Constants.BL_LOOP_BODY)){
                    ignoreBranch = true;
                    
                    if(verbose){
                        log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "Inference will ignore right branch of target: " + block.followers().get(1).toString());
                    }

                }
            }
            
        }
        {
            for(BasicBlock b : block.followers()){
                    if(b.id().toString().contains(Constants.BL_LOOP_END)){
                        ignoreBranch = true;
                        
                        if(verbose){
                            log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "Inference will ignore right branch of target: " + block.followers().get(1).toString());
                        }
                    }
                }
        }
        
        if(ignoreBranch && verbose){
            log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "Inference will ignore else branch target for block: " + block.id().toString());
        }
        
        // handle the if statement
        if(block.followers().size() == 2 && ignoreBranch==false){

            //
            // Before we branch, we need to determine if the 
            // subtree we are looking at will contain any useful propositions. 
            // We do this by searching in the subtree, stopping at the least common ancestor
            // of the two (possible) nodes. 
            // 
            
            BasicBlock left  = block.followers().get(0);
            BasicBlock right = block.followers().get(1);
            
            BasicBlock lca = lca(left, right); // this must ALWAYS be true. 
            
            if(lca==null || true){
                
                //TODO - need to investigate what conditions LCA can't be 
                //       found.
                
                depth++;
                Prop<JCExpression> e =  Or.of(
                        sp(p, block.followers().get(0)), 
                        sp(p, block.followers().get(1))
                        );
                depth--;
                
                
                log.noticeWriter.println("[STRONGARM] Cannot find an LCA for BasicBlocks " + left.id() + " and " + right.id());

                return e;

            }
            
            if(verbose){
                log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + String.format("Found LCA=%s for blocks L=%s, R=%s", lca.id().toString(), left.id().toString(), right.id().toString()));
            }
            
            int propsInLeftSubtree = propsInSubtree(left, lca);
            int propsInRightSubtree = propsInSubtree(right, lca);

            if(verbose){
                log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + String.format("Props in Subtrees L=%d, R=%d", propsInLeftSubtree, propsInRightSubtree));
            }

            // 
            // We gain nothing by keeping this subtree
            //
            if(propsInLeftSubtree + propsInRightSubtree == 0){ // skip to LCA
                
                if(verbose){
                    log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "No propositions in either subtree, skipping to LCA=" + lca.id().toString());
                }
                
                return sp(p, lca);
            }
            
            //
            // In both of these cases we limit nesting by removing an OR operator 
            //
            if(propsInLeftSubtree == 0){
                
                if(verbose){
                    log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "No propositions in left subtree, skipping to RIGHT=" + right.id().toString());
                }
               
                return sp(p, right);
            }
            
            if(propsInRightSubtree == 0){
                
                if(verbose){
                    log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "No propositions in right subtree, skipping to LEFT=" + left.id().toString());
                }

                return sp(p, left);
            }

            if(verbose){
                log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "Found propositions in both branches, will take OR");
            }

            // otherwise, this is a valid OR and both branches are included.
            
            depth++;
            Prop<JCExpression> e =  Or.of(
                    sp(p, block.followers().get(0)), 
                    sp(p, block.followers().get(1))
                    );
            depth--;
            return e;
            
        }else if(block.followers().size() > 0){
            return  sp(p, block.followers().get(0));
        }
        
        
        getExitBlocks().add(block);
        
        return p;
    }
    
    private void pickupLexicalMappings(JCStatement stmt, BasicBlock block){

        if(stmt instanceof JmlStatementExpr){
            JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;
        
            if(isAssignStmt(jmlStmt)){
                addSubstitutionAtBlock(jmlStmt.expression, _mappings, block);
                debugLexicalMappings.add(new Object[]{block.id().toString(), jmlStmt.expression.toString()});

            }else if(isPostconditionStmt(jmlStmt)){
                addSubstitutionAtBlock(jmlStmt.expression, _mappings, block);
                debugLexicalMappings.add(new Object[]{block.id().toString(), jmlStmt.expression.toString()});                    
            }else if(isLoopInvariant(jmlStmt) && jmlStmt.expression instanceof JCBinary){
                
                JCBinary jmlBinary = (JCBinary)jmlStmt.expression;
                //TODO -- might have to add filtering for only equalities 
                addSubstitutionAtBlock(jmlStmt.expression, _mappings, block);
                debugLexicalMappings.add(new Object[]{block.id().toString(), jmlStmt.expression.toString()});
            }
            
            if(jmlStmt.expression instanceof JCBinary && jmlStmt.token==JmlToken.ASSUME && jmlStmt.label == Label.IMPLICIT_ASSUME){
                if(jmlStmt.toString().contains(Strings.newArrayVarString)){

                    JCBinary binExpr = (JCBinary)jmlStmt.expression;
                   
                    if(binExpr.rhs.toString().contains(Strings.tmpVarString)){
                        
                        JCExpression expr = treeutils.makeBinary(0, JCTree.EQ, binExpr.rhs, binExpr.lhs);
                    
                        addSubstitutionAtBlock(expr, _mappings, block);
                        debugLexicalMappings.add(new Object[]{block.id().toString(), expr.toString()});
                    }
                }
            }
            
        }else if(isVarDecl(stmt)){
            JmlVariableDecl decl = (JmlVariableDecl)stmt;
            addSubstitutionAtBlock(decl, _mappings, block);
            debugLexicalMappings.add(new Object[]{block.id().toString(), decl.toString()});
        } 
      
    }
    private int propsInSubtree(BasicBlock block, BasicBlock lca){

        if(lca.id()==block.id()){
            return 0;
        }
        
        int props = 0;
        
        if(skipBlock(block)){
            return 0;
        }
        
        for(JCStatement stmt : block.statements()){        
            if(skip(stmt)){ continue; }
            props++;
        }
        
        
        // handle the if statement
        if(block.followers().size() == 2){
            BasicBlock left  = block.followers().get(0);
            BasicBlock right = block.followers().get(1);
            
            return props + propsInSubtree(left, lca) + propsInSubtree(right, lca);  
            
        }else if(block.followers().size() > 0){
            return props + propsInSubtree(block.followers().get(0), lca);
        }
        
        return props;
    }

    /**
     * Find the least common ancestor of the two nodes.  
     * @param left
     * @param right
     * @return The LCA or null if nothing is found
     */
    private BasicBlock lca(BasicBlock left, BasicBlock right){
        
        for(BasicBlock b : joins){
            if(reachable(b, left) && reachable(b, right)){
                return b;
            }
        }
        
        return null;
    }
    
    /**
     * Determines if a path is reachable from start to end
     * @param start
     * @param end
     * @return true if yes, otherwise no.
     */
    private boolean reachable(BasicBlock start, BasicBlock end){
        if(start==end){
            return true;
        }
        
        for(BasicBlock adjacent : start.preceders()){
            if(reachable(adjacent, end)) return true;
        }
        
        return false;
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
    
    public boolean ignoreBranch(BasicBlock block ){
        
//        if(1==1){
//            return false;
//        }
//        
        int validPropositions = 0;
        
        // we ignore branches on two conditions.
        // 1) The block is being used to set up a precondition check only
        // 2) The block contains no valid propositions
        
        boolean didDefinePrecondition = false;
        
        for(JCStatement stmt : block.statements()){
            
            if(!didDefinePrecondition && stmt instanceof JmlStatementExpr && isPreconditionStmt((JmlStatementExpr)stmt)){
                didDefinePrecondition = true;
            }
            // a single var decl means we DON'T skip the then branch.
            if(!isVarDecl(stmt) && skip(stmt)){ continue; }
            
            
            validPropositions++;
        }
        
        if(didDefinePrecondition){
            return true;
        }
        

        return validPropositions == 0;
        
    }
    
    public boolean skip(JCStatement stmt){
              
        JmlStatementExpr jmlStmt;
        
        if(stmt instanceof JmlStatementExpr){
            jmlStmt = (JmlStatementExpr)stmt;
        }else{
            return true;
        }
        
        if(isAdmissableImplicitAssumption(jmlStmt)){
            return false;
        }
        
        if(isLoopInvariant(jmlStmt)){
            return false;
        }
        
        if(isDSA(jmlStmt)){
            return true;
        }
        
        // we only care about assignments (assumes)
        if(isAssignStmt(jmlStmt)){
            
            if(jmlStmt.expression instanceof JmlBBFieldAssignment){
                return false;
            }
            
            if(jmlStmt.expression instanceof JmlBBArrayAssignment){
                return false;
            }
            
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
            
            if(jmlStmt.expression instanceof JCIdent && preconditionAssertions.contains(((JCIdent)jmlStmt.expression).name.toString())){
                return true;
            }
            
            if(jmlStmt.expression instanceof JCUnary){
            
                JCUnary unaryStmt = (JCUnary)jmlStmt.expression;
                
                if(unaryStmt.arg instanceof JCBinary){
                    if(((JCBinary)unaryStmt.arg).lhs.toString().startsWith("_JML___")){
                        return true;
                    }
                }
                
                if(unaryStmt.arg instanceof JCBinary){
                    if(preconditionAssertions.contains(((JCBinary)unaryStmt.arg).lhs.toString())){
                        return true;
                    }
                }
                
                if(unaryStmt.arg instanceof JCIdent){
                    if(preconditionAssertions.contains(((JCIdent)unaryStmt.arg).name.toString())){
                        return true;
                    }
                }
                
            }
            
            
            return false;
        }
        
        if(isPreconditionStmt(jmlStmt)){ 
            initialPreconditionFound = true;
            return false;
        }
        
        if(isPostconditionStmt(jmlStmt)){ 
            return false;
        }
        
        
            
        return true;
    }
    
    boolean initialPreconditionFound = false;
    
    private boolean isAdmissableImplicitAssumption(JmlStatementExpr expr){
        if(expr.token==JmlToken.ASSUME && expr.label == Label.IMPLICIT_ASSUME && expr.toString().contains("Array_length")){
            return true;
        }
        return false;
    }
    
    private boolean isLoopInvariant(JmlStatementExpr expr){
        if(expr.token==JmlToken.ASSUME &&  expr.label == Label.LOOP_INVARIANT_ASSUMPTION){
            return true;
        }
        return false;
    }
    
    
    private boolean isVarDecl(JCStatement stmt){
        if(stmt instanceof JmlVariableDecl){
            return true;
        }
        return false;
    }
    
    private boolean isDSA(JmlStatementExpr stmt){
        if(stmt.label!=null && stmt.label.info()!=null && stmt.label.info().equals("DSA")){
            return true;
        }
        
        return false;
    }
    private boolean isBranchStmt(JmlStatementExpr stmt){
        if(stmt.label == Label.BRANCHT || stmt.label == Label.BRANCHE || stmt.label == Label.BRANCHC || stmt.label == Label.CASECONDITION){
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
    
    private boolean isPostconditionStmt(JmlStatementExpr stmt){
        if(stmt.label == Label.POSTCONDITION){
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
    private List<Object[]> debugPremapMappings = new ArrayList<Object[]>();
    private List<Object[]> debugLexicalMappings = new ArrayList<Object[]>();
    
    public Object[][] getDebugMappings(){
        Object[][]debugMappings = new Object[debugPremapMappings.size()][3];
        
        for(int i=0; i< debugPremapMappings.size(); i++){
            debugMappings[i] = Arrays.copyOf(debugPremapMappings.get(i), debugPremapMappings.get(i).length);
        }
        
        return debugMappings;
    }

    public Object[][] getLexicalMappings(){
        Object[][]debugMappings = new Object[debugLexicalMappings.size()][2];
        
        for(int i=0; i< debugLexicalMappings.size(); i++){
            debugMappings[i] = Arrays.copyOf(debugLexicalMappings.get(i), debugLexicalMappings.get(i).length);
        }
        
        return debugMappings;
    }

    
    public Map<JCIdent, ArrayList<JCTree>> getBlockerMappings(){
        
        debugPremapMappings.clear();
        
        Map<JCIdent, ArrayList<JCTree>> subs = new HashMap<JCIdent, ArrayList<JCTree>>();
        
        for(BasicBlock b : blocks){
            subs.putAll(getBlockerMappings(b));
        }
        
        return subs;
    }

    
    public Map<JCIdent, ArrayList<JCTree>> getBlockerMappings(BasicBlock b){
        
        Map<JCIdent, ArrayList<JCTree>> subs = new HashMap<JCIdent, ArrayList<JCTree>>();
        
            
        VarMap blockMap  = basicBlocker.blockmaps.get(b);
    
        Set<VarSymbol> syms2 = blockMap.keySet();
        
        log.noticeWriter.println("PREMAP BINDINGS @ BLOCK: " + b.id());
        log.noticeWriter.println("--------------------------");
       
        for(VarSymbol s : syms2){

            debugPremapMappings.add(new Object[]{b.id().toString(), blockMap.getName(s).toString(), s.toString()});
            
            
            //blockMap.getName(s)
            //treeutils.makeSy
            JCIdent replace = treeutils.makeIdent(0, blockMap.getName(s).toString(), s.type);
            JCIdent with    = treeutils.makeIdent(0, s);
            
            JCBinary replacement = treeutils.makeBinary(0, JCTree.EQ, replace, with);
            
            if(verbose){
                log.noticeWriter.println(" --[transformed]--> " + replacement.toString() );
            }
            
            
            addSubstitutionAtBlock(replacement, subs, b);

        }
    

        
        return subs;
    }

    
    
    
    //TODO: not safe to call this more than once.
    public Map<JCIdent, ArrayList<JCTree>> getSubstitutionMappings(){
        
        if(_mappingsDone){
            return _mappings;
        }       
        
        Map<JCIdent, ArrayList<JCTree>> subs = _mappings;

        // reverse internally
        for(JCIdent k : subs.keySet()){
            Collections.reverse(subs.get(k));
        }
        
        _mappingsDone = true;
        
        return subs;        
    }
    
    
    private void initSp(){
        debugLexicalMappings.clear();

        _mappings = new HashMap<JCIdent, ArrayList<JCTree>>();
        loopDepth = 0;
        _mappingsDone = false;
        setExitBlocks(new HashSet<BasicBlock>());
        
    }

    public Set<BasicBlock> getExitBlocks() {
        return exitBlocks;
    }

    private void setExitBlocks(Set<BasicBlock> exitBlocks) {
        this.exitBlocks = exitBlocks;
    }

    public ArrayList<JCTree> getSubstitutionTree(){

        ArrayList<JCTree> subs = new ArrayList<JCTree>();
        
        // get the exit blocks.
        
        return null; //return getSubstitutionTree(b, subs, getSubstitutionMappings());
        
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
}
    
