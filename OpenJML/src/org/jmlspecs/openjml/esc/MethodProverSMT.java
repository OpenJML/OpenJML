package org.jmlspecs.openjml.esc;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.Span;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IPrinter;
import org.smtlib.IResponse;
import org.smtlib.IResponse.IError;
import org.smtlib.IResponse.IPair;
import org.smtlib.ISolver;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.SMT;
import org.smtlib.sexpr.ISexpr;

import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCCase;
import com.sun.tools.javac.tree.JCTree.JCConditional;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCIf;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCSwitch;
import com.sun.tools.javac.tree.JCTree.JCSynchronized;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Position;

public class MethodProverSMT {
    
    final public static String separator = "--------------------------------------";

    // OPTIONS SET WHEN prover() IS CALLED
    
    /** true if counterexample information is desired - set when prove() is called */
    protected boolean showCounterexample;
    
    /** true if counterexample trace information is desired - set when prove() is called */
    protected boolean showTrace;
    
    /** true if subexpression trace information is desired 
     *  - set when prove() is called */
    protected boolean showSubexpressions;
    
    /** The compilation context - cached at construction time */
    final protected Context context;
    
    /** The compiler log for this context - cached at construction time */
    final protected Log log;
    
    /** The Utils instance for this context - cached at construction time */
    final protected Utils utils;
    
    /** The JmlEsc instance that is calling this method prover - cached at construction time */
    final protected JmlEsc jmlesc;
    
    /** The JmlTreeUtils tool for this compilation context - cached at construction time*/
    final protected JmlTreeUtils treeutils;
    
    /** The factory to produce IProverResult objects. This is initialized to use
     * ProverResult in the constructor, but the client can set a different 
     * factory before calls to prove() 
     */
    public IProverResult.IFactory factory;
    
    /** The interface for new ITracer factories */
    public interface ITracerFactory {
        public ITracer makeTracer(Context context, SMT smt, ISolver solver, Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap);
    }
    
    /** The factory to use to create Tracer objects, initialized to the one kind of tracer we currently have. */
    public ITracerFactory tracerFactory = new ITracerFactory() {
        public ITracer makeTracer(Context context, SMT smt, ISolver solver, Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap) {
            return new Tracer(context,smt,solver,cemap,jmap);
        }
    };

    /** A map filled in by running the tracer - it maps String versions of 
     * expressions to a user-friendly String for display in the tracing output.
     * Examples are that null and this would typically be represented by the
     * solver as some internal reference to a solver constant.
     */
    public Map<String,String> constantTraceMap = new HashMap<String,String>();
    
    /** The object to use to trace counterexamples. */
    public ITracer tracer;
    

    // DEBUGGING SETTINGS

    /** local field used to enable verbose output for this object */
    protected boolean verbose;
    
    /** Just for debugging esc */
    public static boolean escdebug = false; // May be set externally to enable debugging while testing
    
    /** true if trace information with respect to the basic block program is to be output
     *  (for debugging only) - set when prove() is called */
    protected boolean showBBTrace;
    

    /** Constructs an instance of this class to do static checking on a method.
     * The instance can be reused for multiple methods and classes
     * within the same compilation context. It does not retain any state of its
     * own, beyond the cached values of other tools in the compilation context.
     */
    public MethodProverSMT(JmlEsc jmlesc) {
        this.jmlesc = jmlesc;
        this.context = jmlesc.context;
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);

        this.factory = new IProverResult.IFactory() {
            @Override
            public IProverResult makeProverResult(MethodSymbol msym, String prover, IProverResult.Kind kind, java.util.Date start) {
                ProverResult pr = new ProverResult(prover,kind,msym);
                pr.methodSymbol = msym;
                if (start != null) {
                    pr.setDuration((pr.timestamp().getTime()-start.getTime())/1000.);
                    pr.setTimestamp(start);
                }
                return pr;
            }
        };
    }
    
    /** Returns the prover exec specified by the options */
    public /*@ nullable */ String pickProverExec(String proverToUse) {
        String exec = JmlOption.value(context, JmlOption.PROVEREXEC);
        if (exec == null) exec = JmlOption.value(context, Strings.proverPropertyPrefix + proverToUse);
        return exec;
    }

    /** The entry point to initiate proving a method. In the current implementation
     * the methodDecl is a method of the original AST and the original AST must
     * already be translated using the JmlAssertionAdder instance that is in
     * jmlesc.assertionAdder. Various information is printed about the proof attempt, and
     * the result of the proof attempt is also returned in an IProverResult object.
     * <P>
     * The amount and kind of printing depends on various options, such as
     * -trace, -subexpressions, -show as well as debugging and verbosity flags.
     */
    public IProverResult prove(JmlMethodDecl methodDecl, String proverToUse) {
        escdebug = escdebug || utils.jmlverbose >= Utils.JMLDEBUG;
        this.verbose = escdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
                || utils.jmlverbose >= Utils.JMLVERBOSE;
        this.showSubexpressions = this.verbose || JmlOption.isOption(context,JmlOption.SUBEXPRESSIONS);
        this.showTrace = this.showSubexpressions || JmlOption.isOption(context,JmlOption.TRACE);
        this.showCounterexample = this.showTrace || JmlOption.isOption(context,JmlOption.COUNTEREXAMPLE);
        this.showBBTrace = escdebug;
        log.useSource(methodDecl.sourcefile);

        boolean print = jmlesc.verbose;
        boolean printPrograms = jmlesc.verbose || JmlOption.isOption(context, JmlOption.SHOW);
        
        JmlClassDecl currentClassDecl = utils.getOwner(methodDecl);
        
        // FIXME - when might methodDecl.sym be null?
        JmlMethodSpecs denestedSpecs = methodDecl.sym == null ? null : 
            JmlSpecs.instance(context).getDenestedSpecs(methodDecl.sym);

        // newblock is the translated version of the method body
        JCBlock newblock = jmlesc.assertionAdder.methodBiMap.getf(methodDecl).getBody();
        if (newblock == null) {
        	log.error("esc.no.typechecking",methodDecl.name.toString()); //$NON-NLS-1$
            return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,null);
        }
        if (printPrograms) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println(separator);
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("TRANSFORMATION OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            log.noticeWriter.println(JmlPretty.write(newblock));
        }

        // determine the executable
        String exec = pickProverExec(proverToUse);
        if (exec == null || exec.trim().isEmpty()) {
            log.error("esc.no.exec",proverToUse); //$NON-NLS-1$
            return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,null);
        }
        
        // create an SMT object, adding any options
        SMT smt = new SMT();
        smt.processCommandLine(new String[]{}, smt.smtConfig);
        Object o = JmlOption.value(context,  JmlOption.TIMEOUT);
        if (o != null && !o.toString().isEmpty()) {
            try {
                smt.smtConfig.timeout = Double.parseDouble(o.toString());
            } catch (NumberFormatException e) {
                // FIXME  - issue a warning
            }
        }

        // Add a listener for errors and start the solver.
        // The listener is set to use the defaultPrinter for printing 
        // SMT abstractions and forwards all informational and error messages
        // to the OpenJML log mechanism
        smt.smtConfig.log.addListener(new SMTListener(log,smt.smtConfig.defaultPrinter));
        SMTTranslator smttrans = new SMTTranslator(context);

        ISolver solver;
        IResponse solverResponse = null;
        BasicBlocker2 basicBlocker;
        BasicProgram program;
        Date start;
        {
            // now convert to basic block form
            basicBlocker = new BasicBlocker2(context);
            program = basicBlocker.convertMethodBody(newblock, methodDecl, denestedSpecs, currentClassDecl, jmlesc.assertionAdder);
            if (printPrograms) {
                log.noticeWriter.println(Strings.empty);
                log.noticeWriter.println(separator);
                log.noticeWriter.println(Strings.empty);
                log.noticeWriter.println("BasicBlock2 FORM of " + utils.qualifiedMethodSig(methodDecl.sym));
                log.noticeWriter.println(program.toString());
            }

            // convert the basic block form to SMT
            ICommand.IScript script = smttrans.convert(program,smt);
            if (printPrograms) {
                try {
                    log.noticeWriter.println(Strings.empty);
                    log.noticeWriter.println(separator);
                    log.noticeWriter.println(Strings.empty);
                    log.noticeWriter.println("SMT TRANSLATION OF " + utils.qualifiedMethodSig(methodDecl.sym));
                    org.smtlib.sexpr.Printer.write(new PrintWriter(log.noticeWriter),script);
                    log.noticeWriter.println();
                    log.noticeWriter.println();
                } catch (VisitorException e) {
                    log.noticeWriter.print("Exception while printing SMT script: " + e); //$NON-NLS-1$
                }
            }

            // Starts the solver (and it waits for input)
            start = new Date();
            solver = smt.startSolver(smt.smtConfig,proverToUse,exec);
            if (solver == null) {
            	log.error("jml.solver.failed.to.start",exec);
        		return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start);
            } else {
            	// Try the prover
            	if (verbose) log.noticeWriter.println("EXECUTION"); //$NON-NLS-1$
            	try {
            		solverResponse = script.execute(solver); // Note - the solver knows the smt configuration
            	} catch (Exception e) {
            		// Not sure there is anything to worry about, but just in case
            		log.error("jml.esc.badscript", methodDecl.getName(), e.toString()); //$NON-NLS-1$
            		return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start);
            	}
            }

        }
        
        // Now assemble and report the result

        if (verbose) {
            log.noticeWriter.println("Proof result is " + smt.smtConfig.defaultPrinter.toString(solverResponse));
        }

        IProverResult proofResult = null;

        {
            IResponse unsatResponse = smt.smtConfig.responseFactory.unsat();
            if (solverResponse.isError()) {
                solver.exit();
                log.error("jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start);
            }
            if (solverResponse.equals(unsatResponse)) {
                if (verbose) log.noticeWriter.println("Method checked OK");
                proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNSAT,start);
                
                if (!JmlOption.value(context,JmlOption.FEASIBILITY).equals("none")) {
                    solver.pop(1); // Pop off previous check_sat

                    java.util.List<JmlStatementExpr> checks = jmlesc.assertionAdder.assumeChecks.get(methodDecl);
                    int k = 0;
                    if (checks != null) for (JmlStatementExpr stat: checks) {
                        ++k;
                        String description = stat.description;
                        solver.pop(1); // Pop off previous setting of assumeCheck
                        solver.push(1); // Mark the top
                        JCExpression bin = treeutils.makeBinary(Position.NOPOS,JCTree.EQ,treeutils.inteqSymbol,
                                treeutils.makeIdent(Position.NOPOS,jmlesc.assertionAdder.assumeCheckSym),
                                treeutils.makeIntLiteral(Position.NOPOS, k));
                        solver.assertExpr(smttrans.convertExpr(bin));
                        solverResponse = solver.check_sat();
                        jmlesc.progress(1,1,"Feasibility check #" + k + " - " + description + " : " +
                                (solverResponse.equals(unsatResponse) ? "infeasible": "OK"));
                        if (solverResponse.equals(unsatResponse)) {
                            if (JmlAssertionAdder.preconditionAssumeCheckDescription.equals(description)) {
                                log.warning(stat.pos(), "esc.infeasible.preconditions", utils.qualifiedMethodSig(methodDecl.sym));
                                proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.INFEASIBLE,start);
                                // If the preconditions are inconsistent, all paths will be infeasible
                                break;
                            } else {
                                log.warning(stat.pos(), "esc.infeasible.assumption", description, utils.qualifiedMethodSig(methodDecl.sym));
                                proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.INFEASIBLE,start);
                            }
                        }
                    }
                }
            } else b: { // Proof was not UNSAT, so there may be a counterexample
                int count = Utils.instance(context).maxWarnings;
                ProverResult pr = (ProverResult)factory.makeProverResult(methodDecl.sym,proverToUse,
                        solverResponse.toString().equals("sat") ? IProverResult.SAT : IProverResult.POSSIBLY_SAT,start);
                proofResult = pr;
                while (true) {

                    if (solverResponse.equals(smt.smtConfig.responseFactory.unknown())) {
                        //IResponse r = solver.get_info(smt.smtConfig.exprFactory.keyword(":reason_unknown")); // Not widely supported
                        // Instead, try to get a simple value and see if there is a model
                        IResponse r = solver.get_value(smt.smtConfig.exprFactory.symbol("NULL"));
                        if (r.isError()) {
                            String msg = ": ";
                            if (JmlOption.value(context,JmlOption.TIMEOUT) != null) msg = " (possible timeout): ";
                            log.warning(methodDecl,"esc.nomodel",msg + r);
                            break b;
                        }
                    }

                    if (print) log.noticeWriter.println("Some assertion is not valid");

                    // FIXME - decide how to show counterexamples when there is no tracing
                    if (showCounterexample && false) {
                        log.noticeWriter.println("\nCOUNTEREXAMPLE");
                        for (VarSymbol v: basicBlocker.premap.keySet()) {
                            Name n = basicBlocker.premap.getName(v);
                            String ns = n.toString();
                            if (ns.equals("this")) continue; // FIXME - use symbols for these
                            if (ns.equals("length")) continue;
                            if (ns.equals("_alloc__")) continue;
                            if (ns.equals("_heap__")) continue;

                            String s = getValue(n.toString(),smt,solver);
                            log.noticeWriter.println(n.toString() + " = " + s);
                        }
                        log.noticeWriter.println(Strings.empty);
                    }
                    
                    Map<JCTree,String> cemap = constructCounterexample(jmlesc.assertionAdder,basicBlocker,smttrans,smt,solver);
                    BiMap<JCTree,JCExpression> jmap = jmlesc.assertionAdder.exprBiMap.compose(basicBlocker.bimap);
                    tracer = tracerFactory.makeTracer(context,smt,solver,cemap,jmap);
                    // Report JML-labeled values and the path to the failed invariant
                    tracer.appendln(JmlTree.eol + "TRACE of " + utils.qualifiedMethodSig(methodDecl.sym));
                    if (showTrace) {
                        log.noticeWriter.println(JmlTree.eol + "TRACE of " + utils.qualifiedMethodSig(methodDecl.sym) + JmlTree.eol);
                        if (utils.jmlverbose  >= Utils.JMLVERBOSE) log.noticeWriter.println("Constants");
                        populateConstantMap(smt, solver, cemap, smttrans);
                    }
                    path = new ArrayList<IProverResult.Span>();
                    JCExpression pathCondition = reportInvalidAssertion(
                            program,smt,solver,methodDecl,cemap,jmap,
                            jmlesc.assertionAdder.pathMap, basicBlocker.pathmap);
                    
                    if (pathCondition != null) {
                        Counterexample ce = new Counterexample(tracer.text(),cemap,path);
                        pr.add(ce); // TODO - make more abstract
                    }
                    
                    if (pathCondition == null) {
                        break;
                    }


                    if (--count <= 0) break;
                    
                    solver.pop(1); // pops off all of the previous check_sat
                    solver.assertExpr(smttrans.convertExpr(pathCondition));
                    solver.push(1); // mark the top again
                    solverResponse = solver.check_sat();

                    if (solverResponse.isError()) {
                        log.error("jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                        return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start);
                    }
                    if (solverResponse.equals(unsatResponse)) break;
                    // TODO -  checking each assertion separately
                }
                pr.setDuration((new Date().getTime() - pr.timestamp().getTime())/1000.);
            }
        }
        solver.exit();
//        jmlesc.mostRecentProgram = program;
        return proofResult;
        
    }
    
    protected List<IProverResult.Span> path;


    public void populateConstantMap(SMT smt, ISolver solver, Map<JCTree,String> cemap,
            SMTTranslator smttrans) {
        addToConstantMap(smttrans.NULL,smt,solver,cemap);
        addToConstantMap(smttrans.thisSym.toString(),smt,solver,cemap);
        for (Type t : smttrans.javaTypes) {
            String s = smttrans.javaTypeSymbol(t).toString(); // FIXME - need official printer
            addToConstantMap(s,smt,solver,cemap);
            s = smttrans.jmlTypeSymbol(t).toString(); // FIXME - need official printer
            addToConstantMap(s,smt,solver,cemap);
        }
    }
    
    public void addToConstantMap(String id, SMT smt, ISolver solver, Map<JCTree,String> cemap) {
        String result = getValue(id,smt,solver);
        if (result != null) constantTraceMap.put(result,id);
        if (utils.jmlverbose  >= Utils.JMLVERBOSE) {
            log.noticeWriter.println("\t\t\tVALUE: " + id + "\t === " + 
                    result);
        }

    }
    
    public void addToConstantMap(JCExpression e, Map<JCTree,String> cemap, SMTTranslator smttrans) {
        String result = cemap.get(e);
        String expr = smttrans.convertExpr(e).toString();// TODO - use the pretty printer?
        if (result != null) constantTraceMap.put(result,e.toString()); 
        if (e.type.tag == TypeTags.CHAR) result = showChar(result); 
        if (utils.jmlverbose  >= Utils.JMLVERBOSE) log.noticeWriter.println("\t\t\tVALUE: " + expr + "\t === " + 
                 result);

    }
    
    Set<String> blocks = new java.util.HashSet<String>();
    
    /** Iterates through the basic blocks to find and report the invalid assertion
     * that caused the SAT result from the prover.
     */
    public JCExpression reportInvalidAssertion(BasicProgram program, SMT smt, ISolver solver, JCMethodDecl decl,
            Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap,
            BiMap<JCTree,JCTree> aaPathMap, BiMap<JCTree,JCTree> bbPathMap) {
        exprValues = new HashMap<JCTree,String>();
        blocks.clear();
        JCExpression pathCondition = reportInvalidAssertion(program.startBlock(),smt,solver,decl,0, JmlTreeUtils.instance(context).falseLit,cemap,jmap,aaPathMap,bbPathMap);
        if (pathCondition == null) {
            log.warning("jml.internal.notsobad","Could not find an invalid assertion even though the proof result was satisfiable: " + decl.sym); //$NON-NLS-1$ //$NON-NLS-2$
            return null;
        }
        return pathCondition;
    }
    
    Map<JCTree,String> exprValues = new HashMap<JCTree,String>();
    
    // These strings must mirror the strings used in JmlAsssertionAdder.visitJmlLblExpression
    private final static String prefix_lblpos = Strings.labelVarString + JmlToken.BSLBLPOS.internedName().substring(1) + "_";
    private final static String prefix_lblneg = Strings.labelVarString + JmlToken.BSLBLNEG.internedName().substring(1) + "_";
    private final static String prefix_lbl = Strings.labelVarString + JmlToken.BSLBLANY.internedName().substring(1) + "_";

    public int checkTerminationPosition(String id, int terminationPos) {
        // The BasicBlocker2 implementation creates special RETURN and 
        // THROWS blocks that just hold those statements. Thus we can 
        // identify terminating statements. This is relevant in the situations
        // in which the invalid assertion is a postcondition - then we want
        // to know which path through the method (ending at a return or
        // throws statement) causes the bad postcondition. Note also that
        // a return or throws statement might be overridden by a subsequent
        // return or throws statement in a later finally block.
        
        // The extraction of the terminationPos from the block id depends
        // on the format of the block id as generated in BasicBlocker2
        int k = id.indexOf(BasicBlockerParent.RETURN);
        if (k < 0) k = id.indexOf(BasicBlockerParent.THROW);
        if (k > 0) {
            int kk = BasicBlockerParent.blockPrefix.length();
            terminationPos = Integer.parseInt(id.substring(kk,k));
        }
        return terminationPos;
    }
    
    
    
    /** Helper method for iterating through the basic blocks to find and report the invalid assertion
     * that caused the SAT result from the prover; 
     * Returns true if an invalid assertion was found and reported */
    // How this works: If there is an invalid assertion, then the value of the blockid
    // of the bloc containing that assertion is false; recursively, the blockid
    // is false for any block that has a following block with a false blockid.
    // Thus if there is an invalid assertion the start block is false and there is
    // a path of false blocks to the invalid assertion. There could possibly be
    // other blocks with false ids as well.
    public JCExpression reportInvalidAssertion(BasicProgram.BasicBlock block, SMT smt, ISolver solver, JCMethodDecl decl, int terminationPos, JCExpression pathCondition,
            Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap,
            BiMap<JCTree,JCTree> aaPathMap, BiMap<JCTree,JCTree> bbPathMap) {
        String id = block.id.name.toString();
        if (!blocks.add(id)) {
            Utils.print("Repeating " + id);
        }
        Boolean value = getBoolValue(id,smt,solver);
        if (value == null) {
            // FIXME - error and what to do ?
            return null;
        }
        if (utils.jmlverbose >= Utils.JMLVERBOSE || JmlOption.isOption(context,JmlOption.COUNTEREXAMPLE)) {
            log.noticeWriter.println("Block " + id + " is " + value);  //$NON-NLS-1$//$NON-NLS-2$
        }
        if (value) {
            // The value of the block id is true, so we don't pursue it
            return null;
        }
        terminationPos = checkTerminationPosition(id,terminationPos);
        pathCondition = JmlTreeUtils.instance(context).makeOr(Position.NOPOS,pathCondition,block.id);
        
        //showTrace = true;
        // FIXME - would like to have a range, not just a single position point,
        // for the terminationPos
        for (JCStatement stat: block.statements()) {
            // Report any statements that are JML-labeled
            if (stat instanceof JCVariableDecl) {
                Name n = ((JCVariableDecl)stat).name;
                String ns = n.toString();
                if (ns.startsWith(Strings.labelVarString)) {
                    int k = ns.lastIndexOf("_");
                    if (ns.startsWith(prefix_lblpos)) {
                        Boolean b = getBoolValue(ns,smt,solver);
                        String label = ns.substring(prefix_lblpos.length(),k); 
                        if (b == null) log.warning(stat.pos,"esc.label.value",label,"is unknown"); //$NON-NLS-1$
                        else if (b) log.warning(stat.pos,"esc.label.value",label,b); //$NON-NLS-1$
                    } else if (ns.startsWith(prefix_lblneg)) {
                        Boolean b = getBoolValue(ns,smt,solver);
                        String label = ns.substring(prefix_lblneg.length(),k); 
                        if (b == null) log.warning(stat.pos,"esc.label.value",label,"is unknown"); //$NON-NLS-1$
                        else if (!b) log.warning(stat.pos,"esc.label.value",label,b); //$NON-NLS-1$
                    } else if (ns.startsWith(prefix_lbl)) {
                        String b = getValue(ns,smt,solver);
                        String label = ns.substring(prefix_lbl.length(),k); 
                        if (b == null) log.warning(stat.pos,"esc.label.value",label,"is unknown"); //$NON-NLS-1$
                        else log.warning(stat.pos,"esc.label.value",label,b); //$NON-NLS-1$
                    } else {
                        log.warning(stat.pos,"jml.internal.notsobad","Unknown label: " + ns); //$NON-NLS-1$
                    }
                }
            }
            
            if (showTrace) {
                JCStatement bbstat = stat;
                JCTree origStat = aaPathMap.getr(bbstat);
                String comment = bbstat instanceof JmlStatementExpr &&
                        ((JmlStatementExpr)bbstat).expression instanceof JCLiteral ?
                                ((JCLiteral)((JmlStatementExpr)bbstat).expression).value.toString()
                                : null;
                ifstat: if (origStat != null) {
                    String loc = utils.locationString(origStat.getStartPosition());
                    //String comment = ((JCLiteral)((JmlStatementExpr)bbstat).expression).value.toString();
                    int sp=-2,ep=-2; // The -2 is different from NOPOS and (presumably) any other value that might be generated below
                    int spanType = Span.NORMAL;
                    JCTree toTrace = null;
                    String val = null;
                    if (origStat instanceof JCIf) {
                        toTrace = ((JCIf)origStat).getCondition();
                    } else if (origStat instanceof JCSwitch) {
                        toTrace = ((JCSwitch)origStat).getExpression();
                        sp = toTrace.getStartPosition();
                        ep = toTrace.getEndPosition(log.currentSource().getEndPosTable());
                    } else if (origStat instanceof JCCase) {
                        toTrace = ((JCCase)origStat).getExpression();
                        sp = origStat.getStartPosition();
                        // 8 is the length of "default:"
                        ep = toTrace == null ? sp + 8 : toTrace.getEndPosition(log.currentSource().getEndPosTable());
//                    } else if (origStat instanceof JCCatch) { // catches come as JmlVariableDecls
//                        JCVariableDecl d = ((JCCatch)origStat).param;
//                        sp = origStat.getStartPosition();
//                        ep = d.getEndPosition(log.currentSource().getEndPosTable());
//                        toTrace = null ; // FIXME - not working correctly yet
                    } else if (origStat instanceof JCSynchronized) {
                        toTrace = ((JCSynchronized)origStat).getExpression();
                    } else if (origStat instanceof JmlForLoop) {
                        JmlForLoop s = (JmlForLoop)origStat;
                        sp = s.getStartPosition();
                        ep = s.getStatement().getStartPosition();
                        // FIXME - what about the initalizer etc.
                    } else if (origStat instanceof JmlWhileLoop) {
                        JmlWhileLoop s = (JmlWhileLoop)origStat;
                        sp = s.getStartPosition();
                        ep = s.getStatement().getStartPosition();
                        // FIXME - what about the initalizer etc.
                    } else if (origStat instanceof JmlDoWhileLoop) {
                        JmlDoWhileLoop s = (JmlDoWhileLoop)origStat;
                        sp = s.getCondition().getStartPosition();
                        ep = s.getCondition().getEndPosition(log.currentSource().getEndPosTable());
//                    } else if (origStat instanceof JmlEnhancedForLoop) {
//                        JmlEnhancedForLoop s = (JmlEnhancedForLoop)origStat;
//                        sp = s.getCondition().getStartPosition();
//                        ep = s.getCondition().getEndPosition(log.currentSource().getEndPosTable());
                    } else if (origStat instanceof JmlVariableDecl) {
                        JmlVariableDecl s = (JmlVariableDecl)origStat;
                        sp = s.getStartPosition();
                        ep = s.getEndPosition(log.currentSource().getEndPosTable());
                        toTrace = s.ident;
                        tracer.appendln(loc + " \t" + comment);
                        log.noticeWriter.println(loc + " \t" + comment);
                        if (toTrace != null && showSubexpressions) tracer.trace(s.init);
                        if (toTrace != null && showSubexpressions) tracer.trace(s.ident);
                        break ifstat;
//                    } else if (comment.startsWith("AssumeCheck assertion")) {
//                    	break ifstat;
                    } else {
                        toTrace = origStat;
                    }
                    if (sp == -2) {
                        sp = toTrace.getStartPosition();
                        ep = toTrace.getEndPosition(log.currentSource().getEndPosTable());
                        val = cemap.get(toTrace);
                        spanType = val == null ? Span.NORMAL : val.equals("true") ? Span.TRUE : Span.FALSE;
                    }
                    //log.noticeWriter.println("SPAN " + sp + " " + ep + " " + spanType);
                    if (sp != Position.NOPOS) {
                        if (ep >= sp) path.add(new Span(sp,ep,spanType));
//                        else log.warning(Position.NOPOS,"jml.internal.notsobad","Incomplete position information (" + sp + " " + ep + ") for " + origStat);
                    } else {
//                        log.warning(Position.NOPOS,"jml.internal.notsobad","Incomplete position information (" + sp + " " + ep + ") for " + origStat);
                    }
                    tracer.appendln(loc + " \t" + comment);
                    log.noticeWriter.println(loc + " \t" + comment);
                    if (toTrace != null && showSubexpressions) tracer.trace(toTrace);
                    String s = ((JmlStatementExpr)bbstat).id;
                    if (toTrace != null && s != null) {
                        tracer.appendln("\t\t\t\t" + s + " = " + cemap.get(toTrace));
                        log.noticeWriter.println("\t\t\t\t" + s + " = " + cemap.get(toTrace));
                    }
                    if (comment.startsWith("AssumeCheck assertion")) break ifstat;
                    
                } else if (aaPathMap.reverse.keySet().contains(bbstat)) {
                    String loc = utils.locationString(bbstat.getStartPosition());
                    //String comment = ((JCLiteral)((JmlStatementExpr)bbstat).expression).value.toString();
                    tracer.appendln(loc + " \t" + comment);
                    log.noticeWriter.println(loc + " \t" + comment);
                } else if (comment != null) {
                    tracer.appendln(" \t//" + comment);
                    log.noticeWriter.println(" \t//" + comment);
                }
                
            }
            
            if (showBBTrace) {
                log.noticeWriter.println("STATEMENT: " + stat);
                if (stat instanceof JmlStatementExpr) {
                    JmlStatementExpr x = (JmlStatementExpr)stat;
                    traceSubExpr(x.expression);
                } else if (stat instanceof JCVariableDecl) {
                    JCVariableDecl vd = (JCVariableDecl)stat;
                    Name n = vd.name;
                    if (vd.init != null) traceSubExpr(vd.init);
                    log.noticeWriter.println("DECL: " + n + " === " + getValue(n.toString(),smt,solver));
                }
            }
            if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlToken.ASSERT) {
                JmlStatementExpr assertStat = (JmlStatementExpr)stat;
                JCExpression e = assertStat.expression;
                Label label = assertStat.label;
                if (e instanceof JCTree.JCLiteral) {
                    value = ((JCTree.JCLiteral)e).value.equals(1); // Boolean literals have 0 and 1 value
                } else if (e instanceof JCTree.JCParens) {
                    value = ((JCTree.JCLiteral)((JCTree.JCParens)e).expr).value.equals(1); // Boolean literals have 0 and 1 value
                } else {
                    id = e.toString(); // Relies on all assert statements being reduced to identifiers
                    value = getBoolValue(id,smt,solver);
                }
                if (!value) {
                    pathCondition = JmlTreeUtils.instance(context).makeOr(Position.NOPOS, pathCondition, e);
                    if (terminationPos == 0) terminationPos = decl.pos;

                    JavaFileObject prev = null;
                    int pos = assertStat.pos;
                    if (pos == Position.NOPOS || pos == decl.pos) pos = terminationPos;
                    if (assertStat.source != null) prev = log.useSource(assertStat.source);
                    String extra = Strings.empty;
                    JCExpression optional = assertStat.optionalExpression;
                    if (optional != null) {
                        if (optional instanceof JCTree.JCLiteral) extra = ": " + ((JCTree.JCLiteral)optional).getValue().toString(); //$NON-NLS-1$
                    }
                    if (assertStat.description != null) {
                        extra = ": " + assertStat.description;
                    }
                    
                    
                    int epos = assertStat.getEndPosition(log.currentSource().getEndPosTable());
                    String loc;
                    if (epos == Position.NOPOS || pos != assertStat.pos) {
                        log.warning(pos,"esc.assertion.invalid",label,decl.getName(),extra); //$NON-NLS-1$
                        loc = utils.locationString(pos);
                        tracer.appendln(loc + ": Invalid assertion (" + label + ")");
                    } else {
                        // FIXME - migrate to using pos() for terminationPos as well 
                        log.warning(assertStat.getPreferredPosition(),"esc.assertion.invalid",label,decl.getName(),extra); //$NON-NLS-1$
                        loc = utils.locationString(assertStat.getPreferredPosition());
                        tracer.appendln(loc + ": Invalid assertion (" + label + ")");
                    }
                    // TODO - above we include the optionalExpression as part of the error message
                    // however, it is an expression, and not evaluated for ESC. Even if it is
                    // a literal string, it is printed with quotes around it.
                    if (assertStat.source != null) log.useSource(prev);
                    
                    if (assertStat.associatedPos != Position.NOPOS) {
                        if (assertStat.associatedSource != null) prev = log.useSource(assertStat.associatedSource);
                        log.warning(assertStat.associatedPos, 
                                Utils.testingMode ? "jml.associated.decl" : "jml.associated.decl.cf",
                                loc);
                        tracer.appendln(utils.locationString(assertStat.associatedPos) + ": Associated location");
                        if (assertStat.associatedSource != null) log.useSource(prev);
                    }

                    // Found an invalid assertion, so we can terminate
                    // Negate the path condition
                    return pathCondition; 
                }
            }
        }
        
        // Since we have not found an invalid assertion in this block, we
        // inspect each follower. Since the blocks form a DAG, this will
        // terminate.
        for (BasicBlock b: block.followers()) {
            JCExpression p = reportInvalidAssertion(b,smt,solver,decl,terminationPos,pathCondition,cemap,jmap,aaPathMap,bbPathMap);
            if (p != null) return p;
        }
        return null; // Did not find anything in this block or its followers
    }

    /** Query the solver for the (boolean) value of an id in the current model */
    public Boolean getBoolValue(String id, SMT smt, ISolver solver) {
        String v = getValue(id,smt,solver);
        if (v == null) return null;
        return !v.contains("false");
    }
    
    /** Query the solver for the (int) value of an id in the current model */
    public int getIntValue(String id, SMT smt, ISolver solver) {
        return Integer.parseInt(getValue(id,smt,solver));
    }

    /** Query the solver for any type of value of an id in the current model */
    public String getValue(String id, SMT smt, ISolver solver) {
        org.smtlib.IExpr.ISymbol s = smt.smtConfig.exprFactory.symbol(id);
        IResponse resp = solver.get_value(s);
        if (resp instanceof IResponse.IError) {
            log.error("jml.internal.notsobad", ((IResponse.IError)resp).errorMsg()); //$NON-NLS-1$
            return null;
        } else if (resp == null) {
            log.error("jml.internal.notsobad", "Could not find value of assertion: " + id); //$NON-NLS-1$
            return null;
        } else if (resp instanceof org.smtlib.sexpr.ISexpr.ISeq){
            org.smtlib.sexpr.ISexpr se = ((org.smtlib.sexpr.ISexpr.ISeq)resp).sexprs().get(0);
            if (se instanceof org.smtlib.sexpr.ISexpr.ISeq) se = ((org.smtlib.sexpr.ISexpr.ISeq)se).sexprs().get(1);
            return se.toString();

        } else if (resp instanceof IResponse.IValueResponse) {
            return ((IResponse.IValueResponse)resp).values().get(0).second().toString(); //FIXME use a printer instead of toString()
        } else {
            log.error("jml.internal.notsobad", "Unexpected response on requesting value of assertion: " + smt.smtConfig.defaultPrinter.toString(resp)); //$NON-NLS-1$
            return null;

        }

    }
    

    /** Write out (through log.noticeWriter) the values of the given expression
     * and, recursively, of any subexpressions.
     */
    public void traceSubExpr(JCExpression e) {
        tracer.trace(e);
    }

    protected String showChar(String userString) {
        try {
            int i = Integer.parseInt(userString);
            userString = "'" + (char)i + "' (" + userString + ')';
        } catch (Exception e) {
            // do nothing
        }
        return userString;
    }
        
   
    /** The interface for tracer objects */
    public interface ITracer {
        void trace(JCTree that);
        void append(String s);
        void appendln(String s);
        String text();
    }
    
    /** This class walks the expression subtrees, printing out the value of each
     * subexpression. It is used by creating an instance of the Tracer (using
     * the constructor), and then calling scan() on an AST. scan() is called
     * recursively to find and print all expressions. Statements are not printed
     * but are scanned for any subexpressions.
     */
    // Not static so we have access to getValue
    public class Tracer extends JmlTreeScanner implements ITracer {
        SMT smt;
        ISolver solver;
        Map<JCTree,String> cemap;
        Log log;
        String result;
        StringBuffer traceText = new StringBuffer();
        
        public void append(String s) {
            traceText.append(s);
        }
        
        public void appendln(String s) {
            traceText.append(s);
            traceText.append(Strings.eol);
        }
        
        public void trace(JCTree that) {
            that.accept(this);
        }
        
        public String text() {
            return traceText.toString();
        }
        
        /** Not to be used by callers - this is set false by some visit methods
         * to prevent scan() from printing the value of the expression under
         * scrutiny.
         */
        protected boolean print = true;
        
        public Tracer(Context context, SMT smt, ISolver solver, Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap) {
            this.smt = smt;
            this.solver = solver;
            this.cemap = cemap;
            this.log = Log.instance(context);
        }
        
        public void scan(JCTree that) {
            super.scan(that);
            if (that instanceof JCExpression && !treeutils.isATypeTree((JCExpression)that)) {
                if (print) {
                    String expr = that.toString();
                    String sv = cemap.get(that);
                    String userString = sv == null ? "???" : constantTraceMap.get(sv);
                    if (userString == null) userString = sv;
                    if (that.type.tag == TypeTags.CHAR) userString = showChar(userString);
                    log.noticeWriter.println("\t\t\tVALUE: " + expr + "\t === " + userString);
                }
                else print = true;
            }
        }
        
        /** Declarations are not expressions, but we want to print the final
         * value of the newly declared variable anyway.
         */
        @Override
        public void visitJmlVariableDecl(JmlVariableDecl e) {
            scan(e.init);
            Name n = e.name;
            String sv = cemap.get(e);
            if (sv == null) {
                sv = getValue(n.toString(),smt,solver);
                //log.noticeWriter.println("\t\t\t\tVALUE Retrieved: " + n + " = " + sv);
                cemap.put(e, sv);
            }
            if (e.type.tag == TypeTags.CHAR) sv = showChar(sv); 
            log.noticeWriter.println("\t\t\tVALUE: " + e.sym + " = " + 
                        (sv == null ? "???" : sv));

        }
        
        /** We only scan and print one branch of the conditional, that selected by the
         * condition.
         */
        @Override
        public void visitConditional(JCConditional e) {
            scan(e.cond);
            String sv = cemap.get(e.cond);
            if (sv == null) {
            } else if (sv.equals("true")) {
                scan(e.truepart);
            } else {
                scan(e.falsepart);
            }
        }
        
        /** Overridden to handle short-circuit cases appropriately */
        @Override
        public void visitBinary(JCBinary tree) {
            // Special handling of short-circuit cases
            if (tree.getTag() == JCTree.OR) {
                scan(tree.lhs);
                String v = cemap.get(tree.lhs);
                if ("false".equals(v)) scan(tree.rhs);
            } else if (tree.getTag() == JCTree.AND) {
                scan(tree.lhs);
                String v = cemap.get(tree.lhs);
                if ("true".equals(v)) scan(tree.rhs);
            } else {
                super.visitBinary(tree);
            }
        }

        /** Overridden to handle short-circuit cases appropriately */
        @Override
        public void visitJmlBinary(JmlBinary tree) {
            // Special handling of short-circuit cases
            if (tree.op == JmlToken.IMPLIES) {
                scan(tree.lhs);
                String v = cemap.get(tree.lhs);
                if ("true".equals(v)) scan(tree.rhs);
            } else {
                super.visitJmlBinary(tree);
            }
        }

        /** Scans only subexpressions, so that the tracing of assignments is
         * more intuitive.
         */
        public void scanLHS(JCTree that) {
            if (that == null || that instanceof JCIdent) {
                // skip
            } else if (that instanceof JCFieldAccess) {
                JCFieldAccess fa = (JCFieldAccess)that;
                scan(fa.selected);
            } else if (that instanceof JCArrayAccess) {
                JCArrayAccess aa = (JCArrayAccess)that;
                scan(aa.indexed);
                scan(aa.index);
            } else {
                log.warning(that.pos(), "jml.internal.notsobad", 
                     "Unexpected kind of AST in Tracer.scanLHS: " + that.getClass());
            }
        }

        /** Left-hand sides take special handling; the LHS is evaluated before
         * the RHS, so we can it first. However, we want the final value of the
         * full LHS expression to be printed after all subexpressions. 
         */
        @Override
        public void visitAssign(JCAssign tree) {
            scanLHS(tree.lhs);
            scan(tree.rhs);
        }

        @Override
        public void visitAssignop(JCAssignOp tree) {
            // TODO: AssignOp statements have the annoyance that only the final
            // value of the LHS is reported.
            scanLHS(tree.lhs);
            scan(tree.rhs);
        }

        @Override
        public void visitApply(JCMethodInvocation tree) {
            scanLHS(tree.meth);
            // FIXME - typeArags?
            for (JCExpression a: tree.args) {
                scan(a);
            }
            if (tree.type.tag == TypeTags.VOID) print = false;
        }

        @Override
        public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
            if (tree.token != JmlToken.BSTYPELC) {
                for (JCExpression a: tree.args) {
                    scan(a);
                }
            }
        }

        @Override
        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr tree) {
            // We don't scan the interior of quantified expressions -
            // they don't have concrete values. The value of the
            // expression itself is reported by scan()
        }

        
    }
    
    /** Construct the mapping from original source subexpressions to values in the current solver model. */
    public Map<JCTree,String> constructCounterexample(JmlAssertionAdder assertionAdder, BasicBlocker2 basicBlocker, SMTTranslator smttrans, SMT smt, ISolver solver) {
        boolean verbose = false;
        if (verbose) {
            log.noticeWriter.println("ORIGINAL <==> TRANSLATED");
            for (JCTree e: assertionAdder.exprBiMap.forward.keySet()) {
                if (!(e instanceof JCExpression) && !(e instanceof JCVariableDecl)) continue;
                JCTree v = assertionAdder.exprBiMap.getf(e);
                if (v != null && assertionAdder.exprBiMap.getr(v) == e) {
                    log.noticeWriter.println(e.toString() + " <==> " + v);
                } else {
                    log.noticeWriter.println(e.toString() + " ===> " + v);
                }
            }
            log.noticeWriter.println("\nTRANSLATED <==> BB");
            for (JCTree e: basicBlocker.bimap.forward.keySet()) {
                JCExpression v = basicBlocker.bimap.getf(e);
                if (v != null && basicBlocker.bimap.getr(v) == e) {
                    log.noticeWriter.println(e.toString() + " <==> " + v);
                } else {
                    log.noticeWriter.println(e.toString() + " ===> " + v);
                }
            }
            log.noticeWriter.println("\nBB <==> SMT");
            for (JCExpression e: smttrans.bimap.forward.keySet()) {
                IExpr v = smttrans.bimap.getf(e);
                if (v != null && smttrans.bimap.getr(v) == e) {
                    log.noticeWriter.println(e.toString() + " <==> " + v);
                } else {
                    log.noticeWriter.println(e.toString() + " ===> " + v);
                }
            }
            log.noticeWriter.println("\nORIGINAL <==> SMT");
        }
        IExpr[] ee = new IExpr[1];
        IPrinter p = smt.smtConfig.defaultPrinter;
//        Map<String,String> ce = constructSMTCounterexample(smttrans,solver);
        Map<JCTree,String> values = new HashMap<JCTree,String>();
        for (JCTree t : assertionAdder.exprBiMap.forward.keySet() ) {
            if (t instanceof JmlVariableDecl) t = ((JmlVariableDecl)t).ident;
            if (!(t instanceof JCExpression)) continue;
            // t is the original source expression
            JCTree t1 = assertionAdder.exprBiMap.getf(t);
            // t1 is the result of JmlAssertionAdder, which should be a new AST
            JCExpression t2 = basicBlocker.bimap.getf(t1);
            // t2 is the result of BasicBlocker2, which may have changed AST nodes in place
            if (t2 == null && t1 instanceof JCIdent) t2 = (JCIdent)t1; // this can happen if the Ident ends up being declared in a declaration (such as wtih field or array assignments)

            IExpr smtexpr = smttrans.bimap.getf(t2);
            if (smtexpr == null) continue;
            
            ee[0] = smtexpr;
            String value = null;
            IResponse resp = solver.get_value(ee);
            // FIXME - need to get a single kind of response
            if (resp instanceof ISexpr.ISeq) {
                ISexpr pair = ((ISexpr.ISeq)resp).sexprs().get(0);
                value = p.toString(((ISexpr.ISeq)pair).sexprs().get(1));
//                ce.put(key, value.toString());
            }
            if (resp instanceof IResponse.IValueResponse) {
                IPair<IExpr,IExpr> pair = ((IResponse.IValueResponse)resp).values().get(0);
                value = p.toString(pair.second());
 //               ce.put(key, value.toString());
            }
            if (resp instanceof IError) {
                value = p.toString(resp);
            }
            String t3 = value;

//            String t3 = t2 == null ? null : ce.get(t2.toString());
            values.put(t, t3);
            if (verbose) log.noticeWriter.println(t + " >>>> " + t1 + " >>>> " + t2 + " >>>> " + 
                    smt.smtConfig.defaultPrinter.toString(smtexpr) + " >>>> "+ t3);
        }
        return values;
    }

    /** This is a listener for SMT log and error messages */
    public static class SMTListener implements org.smtlib.Log.IListener {
        org.smtlib.IPrinter printer;
        com.sun.tools.javac.util.Log log;
        
        SMTListener(Log log, org.smtlib.IPrinter printer) {
            this.log = log;
            this.printer = printer;
        }
        
        @Override
        public void logOut(String msg) {
            log.noticeWriter.println(msg);
        }

        @Override
        public void logOut(IResponse result) {
            log.noticeWriter.println(printer.toString(result));
        }

        @Override
        public void logError(String msg) {
            log.error("jml.smt.error",msg); //$NON-NLS-1$
        }

        @Override
        public void logError(IError result) {
            log.error("jml.smt.error",printer.toString(result)); //$NON-NLS-1$
        }

        @Override
        public void logDiag(String msg) {
            log.noticeWriter.println(msg);
        }

        @Override
        public void indent(String chars) {
            // TODO - not sure how to enforce the indent
        }
        
    }
        
    /** This class stores variable - value pairs that constitute a counterexample
     * for a given proof attempt.  For flexibility, both variable and value are 
     * stored as Strings, though this makes it depend on the format of the 
     * rendering to String. It's OK because this information is not persisted.
     */
    public class Counterexample implements IProverResult.ICounterexample {
        protected SortedMap<String,String> map = new TreeMap<String,String>();
        protected Map<JCTree,String> mapv = new HashMap<JCTree,String>();
        private List<IProverResult.Span> path;
        public String traceText;
        
        public Counterexample(String trace, Map<JCTree,String> cemap, List<IProverResult.Span> path) {
            mapv = cemap;
            this.path = path;
            this.traceText = trace;
        }
  
        // FIXME _ Cleanup
//        @Override
//        public void put(String key,String value) {
//            map.put(key,value);
//        }
    //    
//        @Override
//        public void putMap(Map<String,String> map) {
//            this.map.putAll(map);
//        }
    //    
//        @Override
//        public Map<String,String> getMap() {
//            return this.map;
//        }
    //
//        @Override
//        public void put(JCTree expr,String value) {
//            mapv.put(expr,value);
//        }
    //
//        @Override
//        public String get(String key) {
//            return map.get(key);
//        }

        @Override
        public String get(JCTree expr) {
            return mapv.get(expr);
        }

        @Override
        public Set<Map.Entry<String,String>> sortedEntries() {
            return map.entrySet();
        }
        
        @Override
        public void putPath(List<IProverResult.Span> path) {
            this.path = path;
        }
        
        @Override
        public List<IProverResult.Span> getPath() {
            return path;
        }
    }
}


