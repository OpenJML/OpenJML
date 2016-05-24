package org.jmlspecs.openjml.strongarm;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.BasicBlocker2;
import org.jmlspecs.openjml.esc.BasicBlocker2.VarMap;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
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

        TraceElement traceElement = new TraceElement(block);
        
        if(skipBlock(block)){
            return p;
        }
        
        if (verbose) {
            log.noticeWriter.println("[STRONGARM] " + this.getDepthStr() + "Inference at block " + block.id().toString());
        }    
        
        trace.add(traceElement);
        
        for(JCStatement stmt : block.statements()){        
            if(skip(stmt)){ continue; }
            
            JmlStatementExpr jmlStmt = (JmlStatementExpr)stmt;
            
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
                

                p = And.of(p, new Prop<JCExpression>(e1.expression, block));                
                traceElement.addExpr(e1.expression);

//                p = And.of(p, new Prop<JCExpression>(e2.expression, block));                
//                traceElement.addExpr(e2.expression);

                
            }else{
                p = And.of(p, new Prop<JCExpression>(jmlStmt.expression, block));                
                traceElement.addExpr(jmlStmt.expression);
            }
        }
        
        boolean ignoreBranch = ignoreBranch(block);
        
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
            
            if(lca==null){
                log.error("jml.internal", "Cannot find an LCA for BasicBlocks " + left.id() + " and " + right.id());
                return null;
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
        
        return p;
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
        
        // we only care about assignments (assumes)
        if(isAssignStmt(jmlStmt)){
            
            if(jmlStmt.expression instanceof JmlBBFieldAssignment){
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
        
        if(isPreconditionStmt(jmlStmt)){ // && initialPreconditionFound==false){
            initialPreconditionFound = true;
            return false;
        }
            
        return true;
    }
    
    boolean initialPreconditionFound = false;
    
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
    

    public Map<JCIdent, ArrayList<JCTree>> getBlockerMappings(){
        
        Map<JCIdent, ArrayList<JCTree>> subs = new HashMap<JCIdent, ArrayList<JCTree>>();
        
        for(BasicBlock b : blocks){
            
            VarMap blockMap  = basicBlocker.blockmaps.get(b);
        
            Set<VarSymbol> syms2 = blockMap.keySet();
            
            log.noticeWriter.println("PREMAP BINDINGS @ BLOCK: " + b.id());
            log.noticeWriter.println("--------------------------");
           
            for(VarSymbol s : syms2){
                // note we FLIP the ordering here (to do this we create a new equality)
                if(verbose){
                    log.noticeWriter.println(blockMap.getName(s) + " --[maps to]--> " + s.toString() );
                }
                
                
                
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
        }

        return subs;
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
