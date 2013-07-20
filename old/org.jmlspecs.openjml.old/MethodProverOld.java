package org.jmlspecs.openjml.esc;

import java.io.StringWriter;
import java.io.Writer;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.esc.BasicBlocker.Counter;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.esc.MethodProverSMT.Tracer;
import org.jmlspecs.openjml.proverinterface.Counterexample;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICoreIds;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.provers.AbstractProver;
import org.jmlspecs.openjml.provers.CVC3Prover;
import org.jmlspecs.openjml.provers.SimplifyProver;
import org.jmlspecs.openjml.provers.YicesProver;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.parser.JmlFactory;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

public class MethodProverOld {

    /** true if counterexample information is desired */
    boolean showCounterexample;
    
    /** true if counterexample trace information is desired */
    boolean showTrace; // FIXME - need to distinguish computing the trace information (for use in the GUI) vs. printing it out
    
    /** true if trace information with respect to the basic block program is to be output */
    boolean showBBTrace;
    
    /** true if subexpression trace information is desired */
    boolean showSubexpressions;
    

    final public Context context;
    final public Log log;
    final public Utils utils;
    final public JmlEsc jmlesc;
    final public JmlTree.JmlFactory factory;
    final public Symtab syms;
    final public Names names;
    
    // TODO - turn these into options
    static boolean usePush = true;
    static boolean useRetract = false;
    static boolean useSearch = false;
    static boolean useCoreIds = false;
    static boolean useTree = false;
    int timingTest;

    /** Whether to check that key assumptions are feasible */
    public boolean checkAssumptions = true;


    
    // FIXME DOCUMENT
    protected Tracer tracer;
    
    
    protected String proverToUse;


    /** true if compiler options are set to a verbose mode */
    boolean verbose;
    
    /** Just for debugging esc */
    public static boolean escdebug = false; // May be set externally to enable debugging while testing
    

    public MethodProverOld(JmlEsc jmlesc) {
        this.jmlesc = jmlesc;
        this.context = jmlesc.context;
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.factory = JmlTree.Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.names = Names.instance(context);
    }
    
    public IProverResult prove(JmlMethodDecl node) {
        IProverResult proofResult;
        this.checkAssumptions = !JmlOption.isOption(context,JmlOption.NO_RAC_CHECK_ASSUMPTIONS);

        timingTest = 0; // jmlesc.timingTest;
        proverToUse = jmlesc.proverToUse;
        
        boolean verboseProgress = Utils.instance(context).jmlverbose >= Utils.PROGRESS;
        
        if (verboseProgress) 
            jmlesc.progress(1,2,"Starting proof of " + node.sym.owner.flatName() + "." + node.sym + " with prover " + proverToUse);
        Utils.Timer timer = new Utils.Timer();
        
        
        JmlMethodDecl tree = (JmlMethodDecl)node;
        //JmlClassDecl currentClassDecl = JmlSpecs.instance(context).get((ClassSymbol)node.sym.owner).decl;
        JmlClassDecl currentClassDecl = (JmlClassDecl)JmlEnter.instance(context).getEnv((ClassSymbol)node.sym.owner).tree;
        
        // Get the denested specs for the method - FIXME - when might they be null?
        JmlMethodSpecs denestedSpecs = tree.sym == null ? null : jmlesc.specs.getDenestedSpecs(tree.sym);
        
        // Change the log's source file to represent the source for this method
        JavaFileObject source = tree.sourcefile;
        JavaFileObject prev = log.useSource(source);

        boolean ok = false;
        BasicProgram program = null;
            
        try {
            String name = node.sym.owner + "." + node.sym;
            
            if (escdebug) {
                log.noticeWriter.println(JmlPretty.write(tree)); // print the input tree
            }
            boolean doMetrics = false;
            VCmode = 0;
            if (timingTest > 0) doMetrics = false;
            boolean showTimes = false;
            Utils.Timer t = null;
            if (showTimes) t = new Utils.Timer();
            if (doMetrics) {
                boolean a = BasicBlocker.useAssertDefinitions;
                boolean b = BasicBlocker.useAssumeDefinitions;
                try {
                    BasicBlocker.useAssertDefinitions = false;
                    BasicBlocker.useAssumeDefinitions = false;
                    program = BasicBlocker.convertToBasicBlocks(context, tree, denestedSpecs, currentClassDecl);
                    metrics(node,program,name);
                } finally {
                    BasicBlocker.useAssertDefinitions = a;
                    BasicBlocker.useAssumeDefinitions = b;
                }
            }
            if (useTree) VCmode = 1;
            program = BasicBlocker.convertToBasicBlocks(context, tree, denestedSpecs, currentClassDecl);
            
            if (doMetrics || timingTest == 1) metrics(node,program,name);
            if (doMetrics) return new ProverResult(proverToUse,IProverResult.SKIPPED);

            try {
                if (JmlOption.isOption(context,"-show") || escdebug) {
                    program.write(log.noticeWriter); // print the basic block program
                }
                //if (showTimes) log.noticeWriter.println("    ... prep           " +  t.elapsed()/1000.);
                //log.noticeWriter.println("\t\t" + program.blocks().size() + " blocks, " + program.definitions().size() + " definitions, " + program.background().size() + " axioms, " + BasicBlocker.Counter.count(program) + " nodes");
                if (verboseProgress) 
                    jmlesc.progress(1,2,"Prover running on " + node.sym.flatName() + "." + node.sym + " with prover " + proverToUse);
                proofResult = prove(node,program);
                if (showTimes) log.noticeWriter.println("    ... prep and prove " +  t.elapsed()/1000.);
                if (showTimes) {
                    Runtime rt = Runtime.getRuntime();
                    log.noticeWriter.println("    ....... Memory free=" + rt.freeMemory() + "  max="+rt.maxMemory() + "  total="+rt.totalMemory());
                }
            } catch (RuntimeException e) {
                String se = e.toString();
                if (e.getCause() != null) se = e.getCause().toString();
                if (se.length() > 200) se = se.substring(0,200) + " .....";
                log.warning(node.pos(),"esc.prover.failure",se);
                // go on with next 
                proofResult = new ProverResult(proverToUse,IProverResult.ERROR);
                String message = e.getMessage();
                if (e.getCause() != null) message = e.getCause().getMessage();
                if (message != null) proofResult.setOtherInfo(message);
            } catch (Throwable e) {
                String se = e.toString();
                if (e.getCause() != null) se = e.getCause().toString();
                if (se.length() > 200) se = se.substring(0,200) + " .....";
                log.warning(node.pos(),"esc.prover.failure",se);
                System.gc();
                proofResult = new ProverResult(proverToUse,IProverResult.ERROR);
                String message = e.getMessage();
                if (e.getCause() != null) message = e.getCause().getMessage();
                if (message != null) proofResult.setOtherInfo(message);
            }
        } catch (RuntimeException e) {
            log.warning(node.pos(),"esc.vc.prep",e);
            // go on with next 
            proofResult = new ProverResult(proverToUse,IProverResult.ERROR);
            String message = e.getMessage();
            if (e.getCause() != null) message = e.getCause().getMessage();
            if (message != null) proofResult.setOtherInfo(message);
        } catch (Throwable e) {
            log.warning(node.pos(),"esc.vc.prep",e);
            System.gc();
            proofResult = new ProverResult(proverToUse,IProverResult.ERROR);
            String message = e.getMessage();
            if (e.getCause() != null) message = e.getCause().getMessage();
            if (message != null) proofResult.setOtherInfo(message);
        } finally {
            log.useSource(prev);
        }
        //progress(1,1,"Completed proof [" + (ok?"   ":"not") + " proved] of " + node.sym.getQualifiedName() + " [" + timer.elapsed()/1000. + "]");
        if (verboseProgress) {
            String s = proofResult.result().toString();
            if (s.equals("UNSAT")) s = "VALID";
            String message = "Completed proof attempt (" + s + ") of " 
                    + node.sym.owner.flatName() + "." + node.sym // using just node.sym gives the signature 
                    + " [" + timer.elapsed()/1000. + "] using " + proverToUse;
            if (proofResult.otherInfo() != null) {
                message = message + JmlTree.eol + "  (" + proofResult.otherInfo() + ")";
            }
            jmlesc.progress(1,1,message);
        }
        jmlesc.mostRecentProgram = program;
        return proofResult;
        
    }

/** Returns the VC expression for a basic block
 * 
 * @param block the block to convert
 * @return the equivalent expression
 */
public @NonNull JCExpression blockExpr(@NonNull BasicBlock block) {
    java.util.List<JCStatement> statements = block.statements();
    Iterator<JCStatement> iterator = statements.iterator();
    return blockExpr(block,iterator);
}

public void metrics(JCMethodDecl node, BasicProgram program, String name) {
    VCmode = 0;
    int ast = BasicBlocker.Counter.countAST(node.body);
    int sts = BasicBlocker.Counter.countASTStatements(node.body);
    BasicBlocker.Counter c = BasicBlocker.Counter.count(program);
//    VCmode = 1;
//    JCTree f = blockExpr(program.startBlock());
//    int fan = BasicBlocker.Counter.countAST(f) + BasicBlocker.Counter.countx(program);

//    BasicProgram newbp = new BasicProgram();
//    newbp.definitions = program.definitions;
//    newbp.background = program.background;
//    java.util.List<JCStatement> list = new java.util.ArrayList<JCStatement>();
//    newblocks(list,program.startBlock(),program,newbp);
//    int lin = BasicBlocker.Counter.countx(newbp);
//    for (BasicBlock b: newbp.blocks) {
//        lin += BasicBlocker.Counter.countAST(blockExpr(b));
//    }
//    log.noticeWriter.println(ast + " AST; " + c + "  " + fan + " tree; " + lin + " linear; " + program.definitions.size() + " defs :: " + name);
    VCmode = 0;
    
    int oth =  Counter.countx(program);
    int fan1 = fanCount(program).nodes + oth;
    int lin1 = parCount(program,false).nodes + oth;
    int linf = parCount(program,true).nodes + oth;
    log.noticeWriter.println(ast + " AST; " + sts + " statements; " + c + "  " + fan1 + " tree; " + lin1 + " linear; " + linf + " fulllinear; " + (program.definitions.size()+program.pdefinitions.size()) + " defs :: " + name);

}

Map<BasicBlock,Counter> countCache = new HashMap<BasicBlock,Counter>();

public Counter parCount(BasicProgram program, boolean full) {
    countCache.clear();
    Counter c = getParCount(program.startBlock(),program,full);
    c.nodes += c.paths;
    return c;
}

public Counter getParCount(BasicBlock block, BasicProgram program, boolean full) {
    Counter c = countCache.get(block);
    if (c == null) {
        c = parCount(block,program,full);
        //log.noticeWriter.println("CACHE " + block.id + " " + c.paths + " " + c.nodes);
        countCache.put(block,c);
    }
    return c;
}

public Counter parCount(BasicBlock block, BasicProgram program, boolean full) {
    Counter c = new Counter();
    Counter ca = new Counter();
    int n = 0;
    for (JCTree t: block.statements()) {
        t.accept(c);
        //c.nodes++;
        if (full && t instanceof JmlStatementExpr && ((JmlStatementExpr)t).token == JmlToken.ASSERT) {
            ca.add(c);
            n++;
        }
    }
    
//    log.noticeWriter.print(block.id + " " + c.nodes + " ");
//    for (BasicBlock b: block.succeeding) log.noticeWriter.print(" " + b.id);
//    log.noticeWriter.println();
//    
    if (block.followers.size() == 0) {
        ca.add(c);
        n++;
        ca.paths = n;
        return ca;
    }
    Counter cc = new Counter();
    for (BasicBlock b: block.followers) {
        Counter ccc = getParCount(b,program,full);
        for (int i=0; i<ccc.paths; i++) {
            cc.add(c);
        }
        cc.add(ccc);
        n += ccc.paths;
        //cc.nodes ++;
    }
    cc.add(ca);
    cc.paths = n;
    return cc;
}

public Counter fanCount(BasicProgram program) {
    countCache.clear();
    return fanCount(program.startBlock(),program);
}

public Counter getFanCount(BasicBlock block, BasicProgram program) {
    Counter c = countCache.get(block);
    if (c == null) {
        c = fanCount(block,program);
        countCache.put(block,c);
    }
    return c;
}

public Counter fanCount(BasicBlock block, BasicProgram program) {
    Counter c = new Counter();
    c.count(block);
    if (block.followers.size() == 0) {
        //c.nodes++;
        return c;
    }
    for (BasicBlock b: block.followers) {
        c.add(getFanCount(b,program));
        //c.nodes ++;
    }
    return c;
}

//public void newblocks(java.util.List<JCStatement> prefix, BasicBlock block, BasicProgram program, BasicProgram newp) {
//    //log.noticeWriter.println("NEWBLOCKS " + block.id + "   prefix = " + Counter.counts(prefix));
//    java.util.List<JCStatement> p = new java.util.ArrayList<JCStatement>();
//    p.addAll(prefix);
//    for (JCStatement s: block.statements) {
//        p.add(s);
//        if ((s instanceof JmlTree.JmlStatementExpr) && ((JmlTree.JmlStatementExpr)s).token == JmlToken.ASSERT) {
//            BasicBlock bb = new BasicBlock(null);
//            bb.statements.addAll(p);
//            newp.blocks.add(bb);
//            //log.noticeWriter.println(    "  BLOCK-A " + Counter.counts(bb));
//        }
//    }
//    if (block.followers.size() == 0) {
//        BasicBlock bb = new BasicBlock(null);
//        bb.statements.addAll(p);
//        newp.blocks.add(bb);
//        //log.noticeWriter.println(    "  BLOCK-B " + Counter.counts(bb));
//    } else {
//        for (BasicBlock bb: block.followers) {
//            newblocks(p,bb,program,newp);
//        }
//    }
//}

/** Helper method to determine the VC expression for a basic block.
 * 
 * @param block BasicBlock being translated
 * @param iterator an iterator over the statements of the block
 * @return the equivalent VC expression
 */
protected @NonNull JCExpression blockExpr(@NonNull BasicBlock block, @NonNull Iterator<JCStatement> iterator) {
    if (iterator.hasNext()) {
        JCStatement st = iterator.next();
        JCExpression rest = null;
        if (st == targetStatement) {
            if (timingTest == 9) {
                rest = blockExpr(block,iterator);
                JCExpression e = factory.Literal(TypeTags.BOOLEAN,0); // FALSE
                e.type = syms.booleanType;
                e.pos = st.pos;
                e = factory.Binary(JCTree.AND,e,rest);
                e.type = syms.booleanType;
                e.pos = st.pos;
                return e;
            } else {
                JCExpression e = factory.Literal(TypeTags.BOOLEAN,0); // FALSE
                e.type = syms.booleanType;
                e.pos = st.pos;
                return e;
            }
        } else if (st instanceof JmlStatementExpr) {
            rest = blockExpr(block,iterator);
            JmlStatementExpr as = (JmlStatementExpr)st;
            if (as.token == JmlToken.ASSUME) {
                JCExpression e = factory.JmlBinary(JmlToken.IMPLIES,as.expression,rest);
                e.type = syms.booleanType;
                e.pos = as.expression.pos;
                return e;
            } else if (as.token == JmlToken.ASSERT) {
                //JCExpression e = factory.JmlBinary(JmlToken.IMPLIES,as.expression,rest);
                JCExpression e = factory.Binary(JCTree.AND,as.expression,rest);
                e.type = syms.booleanType;
                e.pos = as.expression.pos;
                return e;
            } else if (as.token == JmlToken.COMMENT) {
                // skip
            } else {
                log.error("esc.internal.error","An unexpected statement type in a BasicBlock: " + as.token.internedName());
            }
        } else {
            log.error("esc.internal.error","An unexpected statement type in a BasicBlock: " + st.getClass());
        }
        return rest;
    } else {
        JCExpression expr = factory.Literal(TypeTags.BOOLEAN,1); // TRUE
        expr.type = syms.booleanType;
        if (VCmode == 0) {
            for (BasicBlock follower: block.followers()) {
                JCExpression e = factory.Binary(JCTree.AND,expr,follower.id);
                e.pos = follower.id.pos;
                e.type = syms.booleanType;
                expr = e;
            }
        } else if (VCmode == 1) {
            for (BasicBlock follower: block.followers()) {
                JCExpression fexpr = blockExpr(follower);
                JCExpression e = factory.Binary(JCTree.AND,expr,fexpr);
                e.pos = follower.id.pos;
                e.type = syms.booleanType;
                expr = e;
            }
        }
        return expr;
    }
}

int VCmode = 0;  // 0 - basic blocks; 1 - tree; 2 - parallel

/** Creates an AST node for a new identifier, meant as an auxiliary logical
 * variable in the eventual VC; the identifier has the given type and node
 * position (the given position is not encoded into the identifier name);
 * an associated VarSymbol is also created.
 * @param name the name of the identifier (including any encoded numbers)
 * @param type the Java type of the identifier (e.g. syms.booleanType)
 * @param nodepos the pseudo source position at which to place the node
 * @return the created identifier
 */
protected @NonNull JCIdent newAuxIdent(@NonNull Name name, @NonNull Type type, int nodepos) {
    JCIdent id = factory.Ident(name);
    id.pos = nodepos;
    id.type = type;
    id.sym = new VarSymbol(0,name,type,null);
    // Note: the owner of the symbol is null, because we do not want it to
    // be interpreted as a Java declaration of some sort.
    return id;
}

BasicBlock containingBlock;
JCStatement targetStatement;

public IProver mostRecentProver = null;

/** Initiate proving of the VC for the method.  The given program must be
 * the BasicProgram corresponding to the given method declaration.
 * @param methodDecl the method whose implementation is being proved
 * @param program the basic program corresponding to the method implementation
 */
public IProverResult prove(@NonNull JCMethodDecl methodDecl, @NonNull BasicProgram program) {
    String name = methodDecl.sym.owner + "." + methodDecl.sym;
    
//    log.noticeWriter.println(methodDecl.toString());
//    log.noticeWriter.println(program.toString());


    IProverResult proofResult;
    IProverResult firstProofResult;
    IProver p = null;
    try {
        p = AbstractProver.getProver(context,proverToUse);
        if (p == null) {
            // Error is already reported
            //log.error("esc.no.prover",proverToUse);
            IProverResult r = new ProverResult(proverToUse,IProverResult.ERROR);
            r.setOtherInfo("Failed to create prover");
            return r;
        }
        //jmlesc.mostRecentProver = p;
    } catch (ProverException e) {
        throw new RuntimeException(e);
//        IProverResult r = new ProverResult(proverToUse,IProverResult.ERROR);
//        r.setOtherInfo(e.getMessage());
//        return r;
    }
    try {

        boolean usingSMT = p instanceof org.jmlspecs.openjml.provers.SMTProver;
        
        if (useRetract && !p.supports().retract) { 
            log.error("esc.retract.not.supported",proverToUse);
            p.kill(); 
            return new ProverResult(proverToUse,IProverResult.SKIPPED);
        }
        if (useCoreIds && !p.supports().unsatcore) {
            log.error("esc.unsatcore.not.supported",proverToUse);
            p.kill(); 
            return new ProverResult(proverToUse,IProverResult.SKIPPED);
        }
        if (timingTest >= 15 && p instanceof CVC3Prover) { 
            p.kill(); 
            return new ProverResult(proverToUse,IProverResult.SKIPPED);
        }
        
        Map<Integer,JCExpression> defexpr = new HashMap<Integer,JCExpression>();

        boolean showTimes = timingTest > 0;
        Utils.Timer timer = null;
        if (showTimes) timer = new Utils.Timer();

        for (BasicProgram.BasicBlock block : program.blocks()) {
            p.define(block.id.toString(),syms.booleanType);
        }
        
        // For SMT, not Yices
        if (usingSMT) {
            for (BasicProgram.Definition def: program.definitions()) {
                p.define(def.id.toString(),def.value.type,def.value); // FIXME - define with a define-fun ?
            }
        }
        
//        if (JmlOptionName.isOption(context,"-checkPreconditions")) {
//            // Check that the preconditions are satisfiable
//            // This is here in case one wants a quick smoke test of the 
//            // preconditions.  Normally one would do the general check of
//            // the method, and only if it is successful would one go on to
//            // check that the various assumptions are feasible.
//            p.push();
//            BasicBlock bl = program.startBlock();
//            JCExpression e = blockExpr(bl);
//            e = factory.Unary(JCTree.NOT,e);
//            e.type = syms.booleanType;
//            p.assume(e);
//            IProverResult b = p.check(false);
//            if (b.result() == ProverResult.UNSAT) {
//                log.warning(methodDecl.pos(),"esc.infeasible.preconditions",methodDecl.getName());
//                if (escdebug) log.noticeWriter.println("Invariants+Preconditions are NOT satisfiable in " + methodDecl.getName());
//                // FIXME - print out core ids if available?
//                p.pop();
//                return false;
//            } else {
//                if (verbose) log.noticeWriter.println("Invariants+Preconditions are satisfiable");
//            }
//            p.pop();
//        }
        
        // compute negated start block id
        
        JCExpression negateStart = null;
        if (!(p instanceof SimplifyProver)) {
            JCIdent id = program.startBlock().id();
            negateStart = factory.Unary(JCTree.NOT,id);
            negateStart.type = syms.booleanType;
            Integer idd = p.assume(negateStart);
            defexpr.put(idd,negateStart);
        }

        // send block equations

        containingBlock = null;
        for (BasicBlock bl : program.blocks()) {
            JCExpression e = blockExpr(bl);
            e = factory.JmlBinary(JmlToken.EQUIVALENCE,bl.id,e); 
            e.pos = bl.id.pos;
            e.type = syms.booleanType;
            //log.noticeWriter.println("BLOCK " + bl.id + " " + Counter.countAST(e));
            Integer assertionNumber = p.assume(e);
            defexpr.put(assertionNumber,e);
        }

        // send any other axioms and definitions
        
        int assertionNumber = 0;
        for (JCExpression expr: program.background()) {
            assertionNumber = p.assume(expr);
            defexpr.put(assertionNumber,expr);
        }
        
        Map<JCExpression,Integer> defnum = new HashMap<JCExpression,Integer>();
        if (!usingSMT) {
            for (BasicProgram.Definition def: program.definitions()) {
                JCExpression expr = def.expr(context);
                assertionNumber = p.assume(expr);
                defnum.put(expr,assertionNumber);
                defexpr.put(assertionNumber,expr);
            }
        }

        for (JCExpression expr: program.pdefinitions) {
            assertionNumber = p.assume(expr);
            defnum.put(expr,assertionNumber);
            defexpr.put(assertionNumber,expr);
        }

        if (checkAssumptions && usePush) p.push();

        int assumptionCheck =0;
        if (BasicBlocker.insertAssumptionChecks) { // We have to include this unless no assumption encoding is done
            if (BasicBlocker.useCountedAssumeCheck) {
                JCExpression e = factory.Literal(TypeTags.INT,0);
                e.type = syms.intType;
                e = factory.Binary(JCTree.EQ, program.assumeCheckVar, e);
                e.type = syms.booleanType;
                assumptionCheck = p.assume(e);
                defexpr.put(assumptionCheck,e);
            } else {
                assumptionCheck = p.assume(BasicBlocker.booleanAssumeCheck);
                defexpr.put(assumptionCheck,BasicBlocker.booleanAssumeCheck);
            }
        }

        long time2=0,time3=0;
        
        firstProofResult = proofResult = p.check(true); // FIXME - are details supported by the prover?
        //jmlesc.proverResults.put(methodDecl.sym,proofResult);
        String message = "Prover reported " + proofResult.result() + " for " + methodDecl.sym.owner.flatName() + "." + methodDecl.sym + " with prover " + proverToUse;
        if (proofResult.result() != IProverResult.UNSAT) message = message + JmlTree.eol + "Checking for counterexample information";
        jmlesc.progress(1,2,message);
        //log.noticeWriter.println("Recorded proof for " + methodDecl.sym); log.noticeWriter.flush();

        if (showTimes) {
            time2 = timer.elapsed();
            timer.reset();
        }
        
        boolean ok = !proofResult.isSat();
        if (timingTest > 0 && timingTest < 9) {
            if (showTimes) log.noticeWriter.println("TIMES-" + timingTest + " " + time2 + " " + (proofResult.isSat()?"SAT":"UNSAT") + " :: " + name);
            return proofResult;
        }
        
        Utils.Timer timer2 = new Utils.Timer();
        Utils.Timer timer3 = new Utils.Timer();
        if (proofResult.isSat()) {
            if (showTimes) log.noticeWriter.println("TIMES-" + timingTest + " " + time2 + " SAT :: " + name);
            if (escdebug) log.noticeWriter.println("Method does NOT satisfy its specifications, it appears");
            if (timingTest == 0) {
                proofResult.setOtherInfo(BasicBlocker.TracerBB.trace(context,program,(Counterexample)proofResult.counterexample(),p));
                String cexample = displayCounterexampleInfo(methodDecl, program, p, proofResult);
                if (showCounterexample || escdebug) log.noticeWriter.println(cexample);
            }
            if (mostRecentProver != null) mostRecentProver.kill();
            mostRecentProver = p;
        } else if (proofResult.result() == IProverResult.UNSAT && (timingTest == 10 || timingTest==9)) {
            if (escdebug) log.noticeWriter.println("Method satisfies its specifications (as far as I can tell)");
            p.kill();
            if (!checkAssumptions) return firstProofResult;
            
            int numbad = 0;
            for (BasicBlock blk : program.blocks()) {
                for (JCStatement stt: blk.statements) {
                    if (stt instanceof JmlStatementExpr && ((JmlStatementExpr)stt).label == Label.ASSUME_CHECK) {
                        timer3.reset();
                        targetStatement = stt;
                        containingBlock = blk;

                        JCIdent ek = (JCIdent)((JmlStatementExpr)stt).expression;

                        String eid = ek.name.toString();
                        int pp = eid.lastIndexOf('_');
                        int ps = eid.indexOf('_');
                        int pos = Integer.parseInt(eid.substring(ps+1,pp));
                        String label = eid.substring(pp+1);

                        
                        // Find the block containing the expression to check
                        //                    containingBlock = null;
                        //                    targetStatement = null;
                        //                    outer: for (BasicBlock bl : program.blocks()) {
                        //                        for (JCStatement st: bl.statements) {
                        //                            if (st instanceof JmlStatementExpr && ((JmlStatementExpr)st).expression == ek) {
                        //                                targetStatement = st;
                        //                                containingBlock = bl;
                        //                                break outer;
                        //                            }
                        //                        }
                        //                    }
                        //                    if (containingBlock == null) {
                        //                        log.noticeWriter.println("COULD NOT FIND ASSUMPTION");
                        //                        continue;
                        //                    }

                        Set<BasicBlock> neededBlocks = new HashSet<BasicBlock>();
                        List<BasicBlock> todo = new LinkedList<BasicBlock>();
                        todo.add(containingBlock);
                        while (!todo.isEmpty()) {
                            BasicBlock b = todo.remove(0);
                            if (neededBlocks.contains(b)) continue;
                            todo.addAll(b.preceders);
                            neededBlocks.add(b);
                        }
                        
                        p = AbstractProver.getProver(context,proverToUse);
                        defexpr = new HashMap<Integer,JCExpression>();
                        
//                        for (BasicProgram.BasicBlock block : program.blocks()) {
//                            p.define(block.id.toString(),syms.booleanType);
//                        }

                        // send negated start block id

                        if (!(p instanceof SimplifyProver)) {
                            Integer idd = p.assume(negateStart);
                            defexpr.put(idd,negateStart);

                        }

                        // send block equations

                        for (BasicBlock bl : program.blocks()) {
                            JCExpression e = factory.Literal(TypeTags.BOOLEAN,1);  // TRUE
                            if (timingTest == 9 || neededBlocks.contains(bl)) {
                                e = blockExpr(bl);
                            }
                            e = factory.JmlBinary(JmlToken.EQUIVALENCE,bl.id,e); 
                            e.pos = bl.id.pos;
                            e.type = syms.booleanType;
                            //log.noticeWriter.println("BLOCK " + bl.id + " " + Counter.countAST(e));
                            Integer idd = p.assume(e);
                            defexpr.put(idd,e);

                        }

                        // send any other axioms and definitions

                        assertionNumber = 0;
                        for (JCExpression expr: program.background()) {
                            assertionNumber = p.assume(expr);
                            defexpr.put(assertionNumber,expr);
                        }

                        defnum = new HashMap<JCExpression,Integer>();
                        for (BasicProgram.Definition def: program.definitions()) {
                            JCExpression expr = def.expr(context);
                            assertionNumber = p.assume(expr);
                            defnum.put(expr,assertionNumber);
                            defexpr.put(assertionNumber,expr);
                        }
                        for (JCExpression expr: program.pdefinitions) {
                            assertionNumber = p.assume(expr);
                            defnum.put(expr,assertionNumber);
                            defexpr.put(assertionNumber,expr);
                        }

                        if (BasicBlocker.insertAssumptionChecks) { // We have to include this unless no assumption encoding is done
                            JCExpression e = factory.Literal(TypeTags.INT,0);
                            e.type = syms.intType;
                            e = factory.Binary(JCTree.EQ, program.assumeCheckVar, e);
                            e.type = syms.booleanType;
                            assumptionCheck = p.assume(e);
                            defexpr.put(assumptionCheck,e);
                        }

                        proofResult = p.check(true);
                        if (escdebug) log.noticeWriter.println("CHECKING " + assumptionCheck + " " + assertionNumber);
                        if (!proofResult.isSat() && timingTest == 0) {
                            reportAssumptionProblem(label,pos,utils.qualifiedMethodSig(methodDecl.sym));
                            if (escdebug) log.noticeWriter.println(label + " " + proofResult.coreIds());
                            proofResult.result(IProverResult.INCONSISTENT);
                        } else {
                            
                        }
                        if (!proofResult.isSat()) {
                            numbad++;
                        }
                        p.kill();
                        long t3 = timer3.elapsed();
                        //log.noticeWriter.println("CHECKING " + eid + " " + r.isSat() +  " " + t3);

                    }
                }
            }

            if (showTimes) {
                time3 = timer.elapsed();
                log.noticeWriter.println("TIMES-" + timingTest + " " + time2 + " " + time3 + " UNSAT checks: " + program.assumptionsToCheck.size() + " " + numbad + " " + (-1) + " :: " + name);
            }

        } else if (proofResult.result() == IProverResult.UNSAT && timingTest == 15 && !(p instanceof CVC3Prover)) {
            if (escdebug) log.noticeWriter.println("Method satisfies its specifications (as far as I can tell)");
            if (!checkAssumptions) return firstProofResult;
            int numcore = -1;
            int numbad = 0;
            if (usePush) { p.pop();  }
            String pcname = program.assumeCheckVar.sym.toString();
            int num = program.assumptionsToCheck.size();
            List<Integer> list = new ArrayList<Integer>(num);
            JCExpression exx = factory.Literal(TypeTags.BOOLEAN,1); // TRUE
            exx.type = syms.booleanType;
            while (num > 0) {
                timer2.reset();
                if (p instanceof CVC3Prover) {
                    p.push();
                    p.assume(exx);
                }
                proofResult = p.check(true);
                if (!proofResult.isSat()) {
//                    log.noticeWriter.println("CHECKING " + "UNSAT" + " " + r.isSat() + " " + timer2.elapsed());
//                    log.noticeWriter.println("EVERYTHING ELSE IS INFEASIBLE " + num);
                    numbad = num;
                    break;
                }
                String result = ((Counterexample)proofResult.counterexample()).get(pcname);
                if (result == null) {
//                    log.noticeWriter.println("NO RESULT");
                    break;
                }
                if (p instanceof CVC3Prover) p.pop();
//                log.noticeWriter.println("RESULT IS " + result);
                int pos = Integer.parseInt(result);
                JCExpression ex = factory.Binary(JCTree.NE, program.assumeCheckVar, factory.Literal(TypeTags.INT,pos));
                ex.type = syms.booleanType;
                exx = factory.Binary(JCTree.AND,exx,ex);
                exx.type = syms.booleanType;
                if (!(p instanceof CVC3Prover)) p.assume(ex);
                list.add(pos);
                --num;
//                long t2 = timer2.elapsed();
//                log.noticeWriter.println("CHECKING " + result + " " + r.isSat() + " " + t2);
            }
            if (showTimes) {
                time3 = timer.elapsed();
                log.noticeWriter.println("TIMES-" + timingTest + " " + time2 + " " + time3 + " UNSAT checks: " + program.assumptionsToCheck.size() + " " + numbad + " " + (-1) + " :: " + name);
            }
            p.kill();
            for (Map.Entry<JCExpression,String> nme:   program.assumptionsToCheck) {
                String nm = nme.getValue();
                int k = nm.indexOf('$');
                int kk = nm.indexOf('$',k+1);
                int ps = Integer.parseInt(nm.substring(k+1,kk));
                if (list.contains(ps)) continue;
                if (timingTest == 0) {
                    reportAssumptionProblem(nm.substring(kk+1),ps,utils.qualifiedMethodSig(methodDecl.sym));
                    log.noticeWriter.println(nm.substring(kk+1) + " " + proofResult.coreIds());
                    proofResult.result(IProverResult.INCONSISTENT);
                }
            }
            
        } else if (proofResult.result() == IProverResult.UNSAT) {  // 0, 11, 12, 13, 14, 16, 17
            if (escdebug) log.noticeWriter.println("Method satisfies its specifications (as far as I can tell)");
            if (!checkAssumptions) return firstProofResult;
            
            //boolean useCoreIds = true; // FIXME - use an option
            //if (timingTest > 0) useCoreIds = timingTest == 11;

            ICoreIds cid = proofResult.coreIds();
            if (useCoreIds && cid == null && verbose) log.noticeWriter.println("Warning: Core ids unexpectedly not returned");
            Collection<Integer> cids = cid == null ? null : cid.coreIds();
            Integer[] ids = new Integer[0];
            if (useCoreIds && cids != null) {
              ids = new Integer[cids.size()]; 
              ids = cids.toArray(ids);
            }
            Arrays.sort(ids);
            int numcore = 0;
            int numbad = 0;
            if (useSearch) numbad = program.assumptionsToCheck.size();
            if (usePush) p.pop();
            String pcname = program.assumeCheckVar.sym.toString();
            JCExpression exx = factory.Literal(TypeTags.BOOLEAN,1);
            exx.type = syms.booleanType;
            for (Map.Entry<JCExpression,String> nm: program.assumptionsToCheck) {
                timer2.reset();
                JCExpression e = nm.getKey();
                String eid = nm.getValue();
                int pp = eid.lastIndexOf('$');
                int ps = eid.indexOf('$');
                int pos = Integer.parseInt(eid.substring(ps+1,pp));
                String label = eid.substring(pp+1);
                if (useCoreIds) {
                    int k = defnum.get(e);
                    int found = Arrays.binarySearch(ids,k);
                    if (found < 0) {
                        // Already not part of the minimal core
                        numcore++;
                        numbad++;
                        //                            if (escdebug || timingTest > 0) log.noticeWriter.println("ALREADY NOT IN MINIMAL CORE: " + pos + " " + label);
                        if (timingTest == 0) {
                            reportAssumptionProblem(label,pos,utils.qualifiedMethodSig(methodDecl.sym));
                            if (escdebug) log.noticeWriter.println(label + " " + proofResult.coreIds());
                            proofResult.result(IProverResult.INCONSISTENT);
                            if (escdebug) minimize(p,defexpr, proofResult.coreIds().coreIds(), assumptionCheck);
                        }
                        continue;
                    }
                }
                if (useSearch) {
                    if (useRetract) {
                        p.retract(assumptionCheck);
                        assumptionCheck = ((YicesProver)p).assumePlus(exx);
                        proofResult = p.check(true);
                    } else if (usePush) {
                        p.push();
                        assumptionCheck = p.assume(exx);
                        proofResult = p.check(true);
                        p.pop();
                    }
                    if (!proofResult.isSat()) {
                        //                              log.noticeWriter.println("CHECKING " + "UNSAT" + " " + r.isSat() + " " + timer2.elapsed());
                        //                              log.noticeWriter.println("EVERYTHING ELSE IS INFEASIBLE " + num);
//                        long t2 = timer2.elapsed();
//                        log.noticeWriter.println("CHECKING " + r.result() + " " + t2 + " " + eid);
                        break;
                    }
                    String result;
                    if (!BasicBlocker.useCountedAssumeCheck) {
                        JCExpression rres = null;
                        for (Map.Entry<JCExpression,String> nmm: program.assumptionsToCheck) {
                            String res = ((Counterexample)proofResult.counterexample()).get(nmm.getValue());
                            if (res == null || res.equals("true")) continue;
                            //log.noticeWriter.println(nmm.getValue() + " IS FALSE " + res);
                            if (hasFeasibleChain(findContainingBlock(nmm.getKey(),program),(Counterexample)proofResult.counterexample())) {
                                //log.noticeWriter.println(nmm.getValue() + " IS FEASIBLE");
                                rres = nmm.getKey();
                                break;
                            }
                        }
                        if (rres == null) {
                            log.noticeWriter.println("NO RESULT");
                            break;
                        }
                        exx = factory.Binary(JCTree.AND,rres,exx);
                        exx.type = syms.booleanType;
                    } else {
                        result = ((Counterexample)proofResult.counterexample()).get(pcname);
                        if (result == null) {
                            //                              log.noticeWriter.println("NO RESULT");
                            break;
                        }
                        int pps = Integer.parseInt(result);
                        JCExpression ex = factory.Binary(JCTree.NE, program.assumeCheckVar, factory.Literal(TypeTags.INT,pps));
                        ex.type = syms.booleanType;
                        exx = factory.Binary(JCTree.AND,ex,exx);
                        exx.type = syms.booleanType;
                    }

                    //                      if (escdebug || timingTest > 0) {
                    //                      if (r.isSat()) {
                    //                          log.noticeWriter.println("NOW SAT - ASSUMPTION WAS OK: " + pos + " " + label);
                    //                      } else {
                    //                          if (useCoreIds) log.noticeWriter.println("STILL UNSAT - CORE WAS NOT MINIMAL - ASSUMPTION WAS INFEASIBLE: " + pos + " " + label);
                    //                          else log.noticeWriter.println("STILL UNSAT - ASSUMPTION WAS INFEASIBLE: " + pos + " " + label);
                    //                      }
                    //                      }
                    //                        if (!r.isSat() && timingTest == 0) {
                    //                            reportAssumptionProblem(label,pos,methodDecl.sym.toString());
                    //                             r.result(IProverResult.INCONSISTENT);
                    //                        }
                    numbad--;
//                    long t2 = timer2.elapsed();
//                    log.noticeWriter.println("CHECKING " + r.result() + " " + t2 + " " + pps);
                } else {
                    JCExpression ex = factory.Binary(JCTree.EQ, program.assumeCheckVar, factory.Literal(TypeTags.INT,pos));
                    ex.type = syms.booleanType;
                    if (useRetract) {
                        p.retract(assumptionCheck);
                        assumptionCheck = ((YicesProver)p).assumePlus(ex);
                        proofResult = p.check(true);
                    } else if (usePush) {
                        p.push();
                        assumptionCheck = p.assume(ex);
                        proofResult = p.check(true);
                        p.pop();
                    }
                    //                      if (escdebug || timingTest > 0) {
//                                          if (r.isSat()) {
//                                              log.noticeWriter.println("NOW SAT - ASSUMPTION WAS OK: " + pos + " " + label);
//                                          } else {
//                                              if (useCoreIds) log.noticeWriter.println("STILL UNSAT - CORE WAS NOT MINIMAL - ASSUMPTION WAS INFEASIBLE: " + pos + " " + label);
//                                              else log.noticeWriter.println("STILL UNSAT - ASSUMPTION WAS INFEASIBLE: " + pos + " " + label);
//                                          }
                    //                  }
                    if (!proofResult.isSat() && timingTest == 0) {
                        reportAssumptionProblem(label,pos,utils.qualifiedMethodSig(methodDecl.sym));
                        if (escdebug) log.noticeWriter.println(label + " " + proofResult.coreIds());
                        proofResult.result(IProverResult.INCONSISTENT);
                        minimize(p, defexpr, proofResult.coreIds().coreIds(), assumptionCheck);
                    }
                    if (!proofResult.isSat()) {
                        numbad++;
                    }
//                    long t2 = timer2.elapsed();
//                    log.noticeWriter.println("CHECKING " + r.result() + " " + t2 + " " + eid);
                }
            }
            if (showTimes) {
                time3 = timer.elapsed();
                log.noticeWriter.println("TIMES-" + timingTest + " " + time2 + " " + time3 + " UNSAT checks: " + program.assumptionsToCheck.size() + " " + numbad + " " + (useCoreIds?numcore:-1) + " :: " + name);
            }
        } else {
            // Result is unknown
            // FIXME - need some tests and more output information here
            if (escdebug) log.noticeWriter.println("Status of method is UNKNOWN - prover failed");
            log.error("esc.proof.failed", proofResult.result(), methodDecl.sym);
            firstProofResult = new ProverResult(proverToUse,IProverResult.ERROR);
        }

    } catch (ProverException e) {
        String se = e.mostRecentInput == null ? Strings.empty :e.mostRecentInput;
        if (se.length() > 200) se = se.substring(0,200) + " .......";
        log.warning(methodDecl.pos(),"esc.prover.failure",methodDecl.sym.toString() + ": " + e.getLocalizedMessage() + ":" + se); // FIXME - change to error
        if (escdebug) {
            log.noticeWriter.println("PROVER FAILURE: " + e);
            if (e.mostRecentInput != null) log.noticeWriter.println("INPUT: " + se);
            e.printStackTrace(log.noticeWriter);
        }
        try {
            if (p != null) p.kill();
        } catch (ProverException ee) {
            log.warning(methodDecl.pos(),"esc.internal.error","Failed to kill process: " + ee);
            // Report but ignore any problems in killing
        }
        firstProofResult = new ProverResult(proverToUse,IProverResult.ERROR);
        firstProofResult.setOtherInfo(e.getMessage());
    } catch (Throwable e) {
        log.warning(methodDecl.pos(),"esc.prover.failure",methodDecl.sym.toString() + ": " + e.getLocalizedMessage());
        if (escdebug) log.noticeWriter.println("PROVER FAILURE: " + e.getClass() + " " + e);
        e.printStackTrace(log.noticeWriter);
        firstProofResult = new ProverResult(proverToUse,IProverResult.ERROR);
        // FIXME - set other info?
    }
    // FIXME - dmz: I added this extra kill to fix Yices processes hanging around
    // on OS X and causing problems for unit tests ("resource not available"), but
    // there should be some other way to just make sure that the process is always
    // dead when we exit this method.
    try {
        if (p != null) p.kill();
    } catch (ProverException e) {
        log.warning(methodDecl.pos(),"esc.internal.error", "Failed to kill process: " + e);
        // ignore any problems in killing
    }
    return firstProofResult;
}

public void minimize(IProver prover, Map<Integer,JCExpression> defexpr, Collection<Integer> coreIds, int assumeCount) {
    if (!escdebug) return;
    Integer[] ids = coreIds.toArray(new Integer[coreIds.size()]);
    Arrays.sort(ids);
    try {
        prover.push();
        // Remove everything but
        for (int i=1; i<=assumeCount; i++) {
            int found = Arrays.binarySearch(ids,i);
            if (found < 0) {
                prover.retract(i);
                log.noticeWriter.println("Retracted " + i);
            }
        }
        IProverResult rr = prover.check(true);
        if (rr.isSat()) {
            log.noticeWriter.println("Redacted problem now satisfiable ??? ");
            return;
        }
        log.noticeWriter.println("Redacted problem still unsatisfiable");
        java.util.List<Integer> keepers = new LinkedList<Integer>();
        for (int i: ids) {
            prover.retract(i);
            rr = prover.check(true);
            log.noticeWriter.println("Retracted " + i + ": " + rr.result());
            if (rr.isSat()) {
                JCExpression e = defexpr.get(i);
                prover.assume(e);
                keepers.add(i);
                log.noticeWriter.println("Restored and keeping " + i );
            } else {
                log.noticeWriter.println("Continuing without restoring " + i );
            }
        }
        log.noticeWriter.println("The following appear to be a contradictory core:");
        for (Integer k: keepers) {
            log.noticeWriter.print(k + "] ");
            JmlPretty pw = new JmlPretty(log.noticeWriter,false);
            defexpr.get(k).accept(pw);
            log.noticeWriter.println(Strings.empty);
        }
        prover.pop();
    } catch (ProverException e) {
        log.noticeWriter.println("Could not retract " + e);
    }
    return;

}


/** For a SAT result, this prints out counterexample information in a human
 * usable form
 * @param methodDecl The declaration of the method being verified
 * @param program The Basic program for that method
 * @param p The prover being used
 * @param r The result from that prover
 */
protected String displayCounterexampleInfo(JCMethodDecl methodDecl,
        BasicProgram program, IProver p, IProverResult r) {
    StringWriter sw = new StringWriter();
    Writer w = sw;
    Counterexample s = (Counterexample)r.counterexample();
    boolean noinfo = true;
    if (s != null) {
        // Find out the termination position; null means that the information
        // was not available from the counterexample - either because the
        // prover did not return it, or because of some bug in the
        // program
        String terminationValue = s.get(BasicBlocker.TERMINATION_VAR);
        int terminationPosition = terminationValue == null ? 0 :
                            Integer.valueOf(terminationValue);
        // Find the assert with the smallest uniqueness number, that is in a feasible block
        //    FIXME - we're presuming that the one with the smallest uniqueness number comes
        //     earliest in the block; subsequent assertions may also be reportable, but if
        //     they come after assumptions, they are suspect
        // Look for "assert$<number>$<number>(@<number>)?$<Label>$<number>"
        Pattern pat1 = Pattern.compile("\\Aassert\\$(\\d+)\\$(\\d+)(@(\\d+))?\\$(\\w+)\\$(\\d+)\\z");
        Matcher found = null;
        int foundNum = Integer.MAX_VALUE;
        for (Map.Entry<String,String> var: s.sortedEntries()) {
            String sname = var.getKey();
            if (!sname.startsWith("assert$")) continue;
            Matcher m = pat1.matcher(sname);
            if (var.getValue().equals("false") && m.find()) {
                Name v = names.fromString(sname);
                BasicBlock bl = findContainingBlock(v,program);
                if (bl == null || hasFeasibleChain(bl,s) ) {
                    int nn = Integer.parseInt(m.group(6));
                    if (nn < foundNum) { foundNum = nn; found = m; }
                    if (escdebug) log.noticeWriter.println("Assertion " + sname + " is false");
                }
            }
        }
        if (found != null) {
            Matcher m = found;
            String sname = m.group(0); // full name of the assertion
            String label = m.group(5); // the label part 
            int usepos = Integer.parseInt(m.group(1)); // the textual location of the assert statement
            int declpos = Integer.parseInt(m.group(2)); // the textual location of associated information (or same as usepos if no associated information)
            JavaFileObject jfo = null;
            String fintstr = m.group(4);
            if (fintstr != null) {
                Integer i = Integer.valueOf(fintstr);
                jfo = BasicBlocker.getFileForInt(i);
            }
            int termpos = usepos;
            if (terminationValue != null &&
                    (Label.POSTCONDITION.toString().equals(label) ||
                            Label.INVARIANT.toString().equals(label) ||
                            Label.CONSTRAINT.toString().equals(label) ||
                            Label.INITIALLY.toString().equals(label) ||
                            Label.SIGNALS.toString().equals(label) ||
                            Label.SIGNALS_ONLY.toString().equals(label))) {
                // terminationPosition is, 
                // if positive, the source code location of the return statement,
                // if negative, the negative of the source code location of
                //          the throw statement or method call of an exception exit
                // if 0, the method exits out the end of the block.  
                // In this last case, one would like to point the
                // error message to the end of the block, but since
                // we do not at the moment have support for 
                // end positions, we use the position of the 
                // method declaration. (TODO)
                if (terminationPosition == 0) termpos = usepos; 
                else if (terminationPosition > 0) termpos = terminationPosition;
                else                             termpos = -terminationPosition;
            }
            Name v = names.fromString(sname);
            BasicBlock bl = findContainingBlock(v,program);
            // A 'false' assertion is spurious if it happens in a block 
            // which is not executed (its block variable is 'true')
            // So we list the assertion if
            //      - we cannot find a block containing the assertion (just to be safe)
            //      - we find a block but find no value for the block variable (just to be safe)
            //      - the block variable is 'false' (not 'true') and there is a chain of false blocks back to the beginning
            if (bl == null || hasFeasibleChain(bl,s) ) {
                if (declpos != termpos || jfo != null) {

                    JavaFileObject prev = log.currentSourceFile();
                    // The suppress call here suppresses reporting warnings, but not actually testing them.
                    // We moved the suppression to avoid putting assert tests in, but here is where to 
                    // turn off the reporting.
//                  if (Nowarns.instance(context).suppress(log.currentSource(), termpos, label)) {
//                      // nothing to do
//                  } else 
                    {
                        log.warning(termpos,"esc.assertion.invalid",label,methodDecl.getName(), Strings.empty);
                        String loc = utils.locationString(termpos);
                        
                        if (jfo != null) log.useSource(jfo);
                        log.warning(declpos,
                        		Utils.testingMode ? "jml.associated.decl": "jml.associated.decl.cf",
                        		loc);

                   }
                    log.useSource(prev);
                } else {
                    log.warning(termpos,"esc.assertion.invalid",label,methodDecl.getName(), Strings.empty);
                }
                //if (declpos != usepos) Log.printLines(log.noticeWriter,"Associated information");
                noinfo = false;
            }
        }

    }

    if (noinfo) {
        log.warning(methodDecl.pos(),"esc.method.invalid",methodDecl.getName());
    } else {
        Pattern pat2 = Pattern.compile("^\\$\\$LBLPOS\\$(\\d+)\\$([^ ]+)");
        for (Map.Entry<String,String> var: s.sortedEntries()) {
            Matcher m = pat2.matcher(var.getKey());
            if (var.getValue().equals("true") && m.find()) {
                int pos = Integer.parseInt(m.group(1));
                String label = m.group(2);
                log.warning(pos,"esc.label",label);
                if (escdebug) log.noticeWriter.println("Label " + label + " has value " + var.getValue());
            }
        }
        Pattern pat3 = Pattern.compile("^\\$\\$LBLNEG\\$(\\d+)\\$([^ ]+)");
        for (Map.Entry<String,String> var: s.sortedEntries()) {
            Matcher m = pat3.matcher(var.getKey());
            if (var.getValue().equals("false") && m.find()) {
                int pos = Integer.parseInt(m.group(1));
                String label = m.group(2);
                log.warning(pos,"esc.label",label);
                if (escdebug) log.noticeWriter.println("Label " + label + " has value " + var.getValue());
            }
        }
        Pattern pat4 = Pattern.compile("^\\$\\$LBLANY\\$(\\d+)\\$([^ ]+)");
        for (Map.Entry<String,String> var: s.sortedEntries()) {
            Matcher m = pat4.matcher(var.getKey());
            if (m.find()) {
                int pos = Integer.parseInt(m.group(1));
                String label = m.group(2);
                log.warning(pos,"esc.label.value",label,var.getValue());
                if (escdebug) log.noticeWriter.println("Label " + label + " has value " + var.getValue());
            }
        }
    }
    String result = Strings.empty;
    
    if (showTrace || escdebug) {
        log.noticeWriter.println("Trace " + methodDecl.getName());
        //BasicBlocker.Tracer.trace(context,methodDecl,s);
        log.noticeWriter.println(result = BasicBlocker.TracerBB.trace(context,program,s,p));
    }
    if (showCounterexample || escdebug) {
        log.noticeWriter.println("Counterexample:");
        // Just some arbitrary number of spaces used to format lines
        String spaces = "                                ";
        for (Map.Entry<String,String> var: s.sortedEntries()) {
            int k = var.getKey().length();
            if (k >= spaces.length()) k = spaces.length()-1;
            log.noticeWriter.println("    " + var.getKey() + spaces.substring(k) + var.getValue());
        }
    }
    return result;
}

/** Reports the details of a problem when an assumption is infeasible.
 * This happens when the assumption is not needed, which is known when
 * the program is still valid (the VC is unsatisfiable) with a false
 * assertion following the assumption.
 * 
 * @param label the label given to the assumption
 * @param pos   the textual position of the associated statement
 * @param methodSignature the name or signature of the method being tested
 */
public void reportAssumptionProblem(String label, int pos, String methodSignature) {
    // The suppress call here suppresses reporting warnings, but not actually testing them.
    // We moved the suppression to avoid putting assert tests in, but here is where to 
    // turn off the reporting.
    //if (Nowarns.instance(context).suppress(log.currentSource(), pos, label)) return;
    if (label.equals(Label.BRANCHT.toString())) {
        log.warning(Math.abs(pos),"esc.infeasible.branch","then",methodSignature);
        if (escdebug) log.noticeWriter.println("Branch is infeasible at " + pos);
    } else if (label.equals(Label.BRANCHE.toString())) {
        log.warning(Math.abs(pos),"esc.infeasible.branch","else",methodSignature);
        if (escdebug) log.noticeWriter.println("Branch is infeasible at " + pos);
    } else if (label.equals(Label.CASECONDITION.toString())) {
        log.warning(Math.abs(pos),"esc.infeasible.case",methodSignature);
        if (escdebug) log.noticeWriter.println("Switch case is infeasible at " + pos);
    } else if (label.equals(Label.PRECONDITION.toString())) {
        log.warning(Math.abs(pos),"esc.infeasible.preconditions",methodSignature);
        if (escdebug) log.noticeWriter.println("Preconditions are infeasible at " + pos);
    } else {
        log.warning(pos,"esc.infeasible.assumption",methodSignature);
        if (escdebug) log.noticeWriter.println("Assumption (" + label + ") is infeasible");
    }
}

/** Checks to see if the given BasicBLock has a feasible chain back to the
 * program start, within the set of variable assignments given in a
 * counterexample.  A BasicBlock is feasible if its block variable is 'false' in
 * the counterexample and either it is the start block or it follows a
 * feasible block.
 * @param bl the BasicBlock to check
 * @param s the counterexample whose assignments to use
 * @return true if feasible, false if not
 */
public boolean hasFeasibleChain(/*@ non_null*/ BasicBlock bl, /*@ non_null*/ Counterexample s) {
    if ("true".equals(s.get(bl.id.name.toString()))) return false;
    if (bl.preceders.size() == 0) return true; // presuming it is the start block, which may not be the case?? FIXME
    for (BasicBlock b: bl.preceders) {
        if (hasFeasibleChain(b,s)) return true;
    }
    return false;
}

/** Finds the basic block containing an assertion with the given name
 * 
 * @param assertName the name of the assertion as used in the definition
 * @param program the basic program in which to find the block
 * @return the BasicBlock in which the assertion occurs, or null if not found
 */
public /*@ nullable */ BasicBlock findContainingBlock(/*@ non_null*/ Name assertName, /*@ non_null*/ BasicProgram program) {
    for (BasicBlock block: program.blocks) {
        for (JCStatement st: block.statements) {
            if ((st instanceof JmlStatementExpr) &&
                    ((JmlStatementExpr)st).token == JmlToken.ASSERT) {
                JCExpression expr = ((JmlStatementExpr)st).expression;
                if ((expr instanceof JCIdent) &&
                        ((JCIdent)expr).name == assertName) return block;
            }
        }
    }
    return null;
}

public /*@ nullable */ BasicBlock findContainingBlock(/*@ non_null*/ JCExpression expression, /*@ non_null*/ BasicProgram program) {
    for (BasicBlock block: program.blocks) {
        for (JCStatement st: block.statements) {
            if ((st instanceof JmlStatementExpr) &&
                    ((JmlStatementExpr)st).token == JmlToken.ASSERT) {
                if (expression == ((JmlStatementExpr)st).expression) return block;
            }
        }
    }
    return null;
}

///** Returns the VC expression for a basic block
// * 
// * @param block the block to convert
// * @return the equivalent expression
// */
//public @NonNull JCExpression blockExpr(@NonNull BasicBlock block) {
//    java.util.List<JCStatement> statements = block.statements();
//    Iterator<JCStatement> iterator = statements.iterator();
//    return blockExpr(block,iterator);
//}
//
//public void metrics(JCMethodDecl node, BasicProgram program, String name) {
//    VCmode = 0;
//    int ast = BasicBlocker.Counter.countAST(node.body);
//    int sts = BasicBlocker.Counter.countASTStatements(node.body);
//    BasicBlocker.Counter c = BasicBlocker.Counter.count(program);
////    VCmode = 1;
////    JCTree f = blockExpr(program.startBlock());
////    int fan = BasicBlocker.Counter.countAST(f) + BasicBlocker.Counter.countx(program);
//
////    BasicProgram newbp = new BasicProgram();
////    newbp.definitions = program.definitions;
////    newbp.background = program.background;
////    java.util.List<JCStatement> list = new java.util.ArrayList<JCStatement>();
////    newblocks(list,program.startBlock(),program,newbp);
////    int lin = BasicBlocker.Counter.countx(newbp);
////    for (BasicBlock b: newbp.blocks) {
////        lin += BasicBlocker.Counter.countAST(blockExpr(b));
////    }
////    log.noticeWriter.println(ast + " AST; " + c + "  " + fan + " tree; " + lin + " linear; " + program.definitions.size() + " defs :: " + name);
//    VCmode = 0;
//    
//    int oth =  Counter.countx(program);
//    int fan1 = fanCount(program).nodes + oth;
//    int lin1 = parCount(program,false).nodes + oth;
//    int linf = parCount(program,true).nodes + oth;
//    log.noticeWriter.println(ast + " AST; " + sts + " statements; " + c + "  " + fan1 + " tree; " + lin1 + " linear; " + linf + " fulllinear; " + (program.definitions.size()+program.pdefinitions.size()) + " defs :: " + name);
//
//}

    public void doTiming(JmlMethodDecl methodDecl) {
        // Old custom translation implementation
        // TODO - review all this - have a way to time all checking
        
        boolean doTimingTests = false;
        
        if (escdebug) log.noticeWriter.println(methodDecl.toString()); // print the method

        if (!doTimingTests) {
            timingTest = 0;
            prove(methodDecl);
        } else {
            log.noticeWriter.println("METHOD: " + utils.qualifiedMethodName(methodDecl.sym));
            //int[] timingTests = { 3,  1,2,3,4,5,6,7, 8, 1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8};
            //int[] timingTests = {1, 9,10,11,15,16,17,12,13,14,9,10,11,15,16,17,12,13,14,9,10,11,15,16,17,12,13,14 };
            //int[] timingTests = {1, 9,10,11,9,10,11,9,10,11 };
            int[] timingTests = { 1, 11,16, 11, 16, 11,16,11,16,11,16};
            // 0 = normal default running
            // 1 = with assert, no push, with defs, no evidence
            // 2 = with assert, no push, with defs, evidence  // vs. 1 gives cost of generating proverResults
            // 3 = with assert, push, with defs, no evidence  // vs. 1 gives cost of assumption checking by push/pop and assumeChecks
            // 4 = with assert+, no push, with defs, no evidence // vs. 1 gives cost of assumption checking by retract 
            // 5 = with assert, push, with defs, evidence  // vs. 1 gives cost of assumption checking by push/pop and assumeChecks (when wanting evidence for CEs)
            // 6 = with assert+, no push, with defs, evidence // vs. 1 gives cost of assumption checking by retract (when wanting evidence for CEs)
            // 7 = with assert, no push, no defs, no evidence // vs. 1 gives cost of using definitions
            // 8 = with assert, no push, with defs, no evidence // vs. 1 gives cost of using tree form

            // Would like to measure the cost of using/not using definitions -- but some VCs get too big
            
            // UNSAT - all use assertion defs
            // 9 = like 10, but without truncating VC at a false assert
            // 10 = no evidence, with assert, no push, assume checks and defs, repeated checks with assert false
            // 11 = no evidence, with assert, push, assume checks and defs, repeated assume check with pop
            // 12 = no evidence, with assert+, no push, retract, assume checks and defs, repeated assume check with retract
            // 13 = evidence, with assert+, push, assume checks and defs, use core ids else repeated assume check with pop
            // 14 = evidence, with assert+, no push, retract, assume checks and defs, use core ids else repeated assume check with retract
            // 15 = like 11, but with evidence and with repeated checks for any CE
            // 16 = like 15, but with pushing and popping
            // 17 = like 15, but with retracting
            
            for (int ttest : timingTests) {
                timingTest = ttest;
                if (ttest >= 9) continue;
                YicesProver.assertPlus = true;
                usePush = true;
                useTree = false;
                BasicBlocker.insertAssumptionChecks = true;
                BasicBlocker.useAssertDefinitions = true;
                BasicBlocker.useAssumeDefinitions = true;
                
                if (timingTest > 0) {
                    YicesProver.assertPlus = timingTest == 4 || timingTest == 6 || timingTest == 12 || timingTest == 13 || timingTest == 14 || timingTest == 17;
                    YicesProver.evidence = timingTest == 2 || timingTest == 5 || timingTest == 6 || timingTest == 13 || timingTest == 14 || timingTest >= 15;
                    usePush = timingTest == 3 || timingTest == 5 || timingTest == 11 || timingTest == 13 || timingTest == 15 || timingTest == 16;
                    useRetract = timingTest == 12 || timingTest == 14 || timingTest == 17;
                    useSearch = timingTest == 15 || timingTest == 16 || timingTest == 17;
                    useCoreIds = timingTest == 13 || timingTest == 14;
                    BasicBlocker.insertAssumptionChecks = true;
                    BasicBlocker.useAssertDefinitions = timingTest != 7;
                    BasicBlocker.useAssumeDefinitions = timingTest != 7;
                    useTree = timingTest == 8;
                }
                
                BasicBlocker.useCountedAssumeCheck = timingTest < 13;
                
                prove(methodDecl);
            }
        }
    }



}
