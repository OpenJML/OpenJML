package org.jmlspecs.openjml.esc;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.Stack;
import java.util.TreeMap;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.Span;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.smtlib.IAttributeValue;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IPrinter;
import org.smtlib.IResponse;
import org.smtlib.IResponse.IError;
import org.smtlib.IResponse.IPair;
import org.smtlib.ISolver;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.SMT;
import org.smtlib.command.C_assert;
import org.smtlib.command.C_check_sat;
import org.smtlib.command.C_push;
import org.smtlib.sexpr.ISexpr;

import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
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
import com.sun.tools.javac.tree.JCTree.JCLambda;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCSwitch;
import com.sun.tools.javac.tree.JCTree.JCSynchronized;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;

public class MethodProverSMT {
    
    final public static String separator = "--------------------------------------";

    // OPTIONS SET WHEN prover() IS CALLED
    
//    /** true if counterexample information is desired - set when prove() is called */
//    protected boolean showCounterexample;
//    
//    /** true if counterexample trace information is desired - set when prove() is called */
//    protected boolean showTrace;
    
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
    
    /** Starting feasibility check -- purely for debugging */
    static public int startFeasibilityCheck = 0;
    
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

//    /** local field used to enable verbose output for this object */
//    protected boolean verbose;
    
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
                    pr.accumulateDuration((pr.timestamp().getTime()-start.getTime())/1000.);
                    pr.setTimestamp(start);
                }
                return pr;
            }
        };
    }
    
    /** Returns the prover exec specified by the options */
    public /*@ nullable */ String pickProverExec(String proverToUse) {
        org.smtlib.SolverProcess.useMultiThreading = false;
        org.smtlib.SolverProcess.useNotifyWait = false;
        String exec = JmlOption.value(context, JmlOption.PROVEREXEC);
        if (exec == null || exec.isEmpty()) exec = JmlOption.value(context, Strings.proverPropertyPrefix + proverToUse);
        if (exec == null || exec.isEmpty()) {
            String loc = utils.findInstallLocation();
            String os = Utils.identifyOS(context);
            String ex = null;
            ex = proverToUse.replace("z3_","z3-").replace('_','.');
//            if (proverToUse.equals("z3_4_3")) ex = "z3-4.3.";
//            if (proverToUse.equals("z3_4_5")) ex = "z3-4.5.";
//            if (proverToUse.equals("z3_4_6")) ex = "z3-4.6.";
            
            if (loc != null && os != null && ex != null) {
                exec = loc + java.io.File.separator + "Solvers-" + os + java.io.File.separator + proverToUse;
                if (new java.io.File(exec).exists()) return exec;
                exec = loc + java.io.File.separator + "Solvers-" + os + java.io.File.separator + ex + ".";
                for (int i=9; i>=0; --i) {
                    if (new java.io.File(exec + i).exists()) {
                        return exec + i;
                    }
                }
                if (!new java.io.File(exec).exists()) {
                    log.warning("jml.message","Implicit executable does not exist " + exec + "X");
                    exec =  null;
                }
            }
        }
        return exec;
    }
    
    protected ISolver solver = null;
    protected ISolver solver2 = null;
    protected boolean aborted = false;
    
    public void abort() {
        if (solver != null) solver.forceExit();
        if (solver2 != null) solver2.forceExit();
        aborted = true;
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
        boolean verbose = escdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
                || utils.jmlverbose >= Utils.JMLVERBOSE;
        this.showSubexpressions = verbose || JmlOption.isOption(context,JmlOption.SUBEXPRESSIONS);
        boolean showTrace = this.showSubexpressions || JmlOption.isOption(context,JmlOption.TRACE);
        boolean showCounterexample = JmlOption.isOption(context,JmlOption.COUNTEREXAMPLE);
        this.showBBTrace = escdebug;
        log.useSource(methodDecl.sourcefile);
        int prevErrors = log.nerrors;

        boolean print = jmlesc.verbose;
        boolean printPrograms = jmlesc.verbose || JmlOption.includes(context, JmlOption.SHOW, "translated");
        boolean printBB = jmlesc.verbose || JmlOption.includes(context, JmlOption.SHOW, "bb");
        boolean printSMT = jmlesc.verbose || JmlOption.includes(context, JmlOption.SHOW, "smt");
        
        JmlClassDecl currentClassDecl = utils.getOwner(methodDecl);
        
        // FIXME - when might methodDecl.sym be null?
        JmlMethodSpecs denestedSpecs = methodDecl.sym == null ? null : 
            JmlSpecs.instance(context).getDenestedSpecs(methodDecl.sym);

        // newblock is the translated version of the method body
        JmlMethodDecl translatedMethod = jmlesc.assertionAdder.methodBiMap.getf(methodDecl);
        if (translatedMethod == null) {
            log.warning("jml.internal","No translated method for " + utils.qualifiedMethodSig(methodDecl.sym));
            return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.SKIPPED,null);
        }
        JCBlock newblock = translatedMethod.getBody();
        if (newblock == null) {
            JCDiagnostic d = log.factory().error(log.currentSource(), null, "esc.no.typechecking",methodDecl.name.toString());
            log.report(d);
        	//log.error("esc.no.typechecking",methodDecl.name.toString()); //$NON-NLS-1$
            return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,null).setOtherInfo(d);
        }
        if (printPrograms) {
            log.getWriter(WriterKind.NOTICE).println(Strings.empty);
            log.getWriter(WriterKind.NOTICE).println(separator);
            log.getWriter(WriterKind.NOTICE).println(Strings.empty);
            log.getWriter(WriterKind.NOTICE).println("TRANSFORMATION OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            log.getWriter(WriterKind.NOTICE).println(JmlPretty.write(newblock));
        }

        // determine the executable
        String exec = pickProverExec(proverToUse);
        if (exec == null || exec.trim().isEmpty()) {
            //log.error("esc.no.exec",proverToUse); //$NON-NLS-1$
            JCDiagnostic d = log.factory().error(log.currentSource(), null, "esc.no.exec",proverToUse);
            log.report(d);
            return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,null).setOtherInfo(d);
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
        SMTTranslator smttrans = getTranslator(context, methodDecl.sym.toString());

        IResponse solverResponse = null;
        BasicBlocker2 basicBlocker;
        BasicProgram program;
        Date start;
        ICommand.IScript script;
        boolean usePushPop = true; // FIXME - false is not working yet
        {
            // now convert to basic block form
            basicBlocker = new BasicBlocker2(context);
            program = basicBlocker.convertMethodBody(newblock, methodDecl, denestedSpecs, currentClassDecl, jmlesc.assertionAdder);
            if (printBB) {
                log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                log.getWriter(WriterKind.NOTICE).println(separator);
                log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                log.getWriter(WriterKind.NOTICE).println("BasicBlock2 FORM of " + utils.qualifiedMethodSig(methodDecl.sym));
                log.getWriter(WriterKind.NOTICE).println(program.toString());
            }

            // convert the basic block form to SMT
            try {
                try {
                    if (utils.jmlverbose >= Utils.PROGRESS && methodDecl.usedBitVectors && !JmlOption.value(context, JmlOption.ESC_BV).equals("true")) {
                        log.note("jml.message", "Using bit-vector arithmetic");
                    }
                    script = smttrans.convert(program,smt,methodDecl.usedBitVectors);
                } catch (SMTTranslator.JmlBVException e) {
                    if (!Utils.testingMode && utils.jmlverbose >= Utils.PROGRESS) {
                        log.note("jml.message", "Switching to bit-vector arithmetic");
                    }
                    script = new SMTTranslator(context, methodDecl.sym.toString()).convert(program,smt,true);
                }
                if (printSMT) {
                    try {
                        log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                        log.getWriter(WriterKind.NOTICE).println(separator);
                        log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                        log.getWriter(WriterKind.NOTICE).println("SMT TRANSLATION OF " + utils.qualifiedMethodSig(methodDecl.sym));
                        org.smtlib.sexpr.Printer.WithLines.write(new PrintWriter(log.getWriter(WriterKind.NOTICE)),script);
                        log.getWriter(WriterKind.NOTICE).println();
                        log.getWriter(WriterKind.NOTICE).println();
                    } catch (VisitorException e) {
                        log.getWriter(WriterKind.NOTICE).print("Exception while printing SMT script: " + e); //$NON-NLS-1$
                    }
                }
            } catch (SMTTranslator.JmlBVException e) {
                throw e;
            } catch (Exception e) {
                //log.error("jml.internal", "Failed to convert to SMT: " + e);
                JCDiagnostic d = log.factory().warning(log.currentSource(), null, "jml.internal", "Failed to convert to SMT: " + e);
                log.report(d);
                return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,new Date()).setOtherInfo(d);
            }
            // Starts the solver (and it waits for input)
            start = new Date();
            setBenchmark(proverToUse,methodDecl.name.toString(),smt.smtConfig);
            solver = smt.startSolver(smt.smtConfig,proverToUse,exec);
            if (solver == null) { 
            	//log.error("jml.solver.failed.to.start",exec);
                JCDiagnostic d = log.factory().error(log.currentSource(), null, "jml.solver.failed.to.start",exec);
                log.report(d);
        		return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start).setOtherInfo(d);
            } else {
            	// Try the prover
            	if (verbose) log.getWriter(WriterKind.NOTICE).println("EXECUTION"); //$NON-NLS-1$
            	try {
            		solverResponse = script.execute(solver); // Note - the solver knows the smt configuration
            	} catch (Exception e) {
            		// Not sure there is anything to worry about, but just in case
            		//log.error("jml.esc.badscript", methodDecl.getName(), e.toString()); //$NON-NLS-1$
            	    solver.exit();
            	    solver = null;
                    JCDiagnostic d = log.factory().error(log.currentSource(), null, "jml.esc.badscript", methodDecl.getName(), e.toString());
                    log.report(d);
            		return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start).setOtherInfo(d);
            	} finally {
                    if (aborted) {
                    	throw new Main.JmlCanceledException("Aborted by user");
                    }
            	}
            }

        }
        
        // Now assemble and report the result

        if (verbose) {
            log.getWriter(WriterKind.NOTICE).println("Proof result is " + smt.smtConfig.defaultPrinter.toString(solverResponse));
        }

        IProverResult proofResult = null;

        {
            IResponse unsatResponse = smt.smtConfig.responseFactory.unsat();
            if (solverResponse.isError()) {
                if (aborted) {
                    throw new Main.JmlCanceledException("Aborted by user");
                }
                solver.exit();
                //log.error("jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                String msg = smt.smtConfig.defaultPrinter.toString(solverResponse);
                String key = "line ";
                int k = msg.indexOf(key);
                if (k >= 0) {
                    k += key.length();
                    int kk = msg.indexOf(" ",k);
                    try {
                        k = Integer.parseInt(msg.substring(k,kk));
                        String s = script.commands().get(k).toString();
                        msg += "\n>>>" + s;
                    } catch (Exception e) {}  // skip
                }
                JCDiagnostic d = log.factory().error(log.currentSource(), null, "jml.esc.badscript", methodDecl.getName(), msg);
                log.report(d);
                return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start).setOtherInfo(d);
            }
            String loc = utils.qualifiedNameNoInit(methodDecl.sym);
            if (Utils.testingMode) loc = "";
            if (solverResponse.equals(unsatResponse)) {
                // FIXME - get rid of the next line some time when we can change the test results
                if (!Utils.testingMode) utils.progress(0,1,loc + " Method assertions are validated");

                if (verbose) log.getWriter(WriterKind.NOTICE).println("Method checked OK");
                proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNSAT,start);
                
                if (!Strings.feasibilityContains(Strings.feas_none,context)) {
                    boolean allFeasibilities = Strings.feasibilityContains(Strings.feas_all,context) || Strings.feasibilityContains(Strings.feas_debug,context);
                    if (usePushPop) {
                        solver.pop(1); // Pop off previous check_sat
                    } else {
                        solver.exit();
                    }

                    java.util.List<JmlStatementExpr> checks = jmlesc.assertionAdder.assumeChecks.get(methodDecl);
                    int feasibilityCheckNumber = 0;
                    if (checks != null) for (JmlStatementExpr stat: checks) {
                        if (aborted) {
                        	throw new Main.JmlCanceledException("Aborted by user");
                        }
                        
                        ++feasibilityCheckNumber;
                        if (feasibilityCheckNumber != stat.associatedPos) {
                            log.note("jml.message", "XXX");
                        }
                        if (feasibilityCheckNumber < startFeasibilityCheck) continue;
                        if (prevErrors != log.nerrors) break;
                        
                        // Only do the feasibility check if called for by the feasibility option
                        if (!allFeasibilities && !Strings.feasibilityContains(stat.description,context)) continue;
                            
                        if (!usePushPop) {
                            solver2 = smt.startSolver(smt.smtConfig,proverToUse,exec);
                            if (JmlAssertionAdder.useAssertCount) {
                                List<ICommand> commands = script.commands();
                                commands.remove(commands.size()-1);
                                ICommand c = commands.remove(commands.size()-1);
                                if (c instanceof C_push) {
                                    commands.remove(commands.size()-1);
                                    commands.remove(commands.size()-1);
                                }
                                JCExpression lit = treeutils.makeIntLiteral(Position.NOPOS, feasibilityCheckNumber);
                                JCExpression bin = treeutils.makeBinary(Position.NOPOS,JCTree.Tag.EQ,treeutils.inteqSymbol,
                                        treeutils.makeIdent(Position.NOPOS,jmlesc.assertionAdder.assumeCheckSym),
                                        lit);
                                commands.add(new C_assert(smttrans.convertExpr(bin)));
                                commands.add(new C_check_sat());
                            } else {
                                script = smttrans.convert(program,smt,methodDecl.usedBitVectors);

                            }
//                            if (printPrograms) {
//                                try {
//                                    log.getWriter(WriterKind.NOTICE).println(Strings.empty);
//                                    log.getWriter(WriterKind.NOTICE).println(separator);
//                                    log.getWriter(WriterKind.NOTICE).println(Strings.empty);
//                                    log.getWriter(WriterKind.NOTICE).println("SMT TRANSLATION OF " + utils.qualifiedMethodSig(methodDecl.sym));
//                                    org.smtlib.sexpr.Printer.WithLines.write(new PrintWriter(log.getWriter(WriterKind.NOTICE)),script);
//                                    log.getWriter(WriterKind.NOTICE).println();
//                                    log.getWriter(WriterKind.NOTICE).println();
//                                } catch (VisitorException e) {
//                                    log.getWriter(WriterKind.NOTICE).print("Exception while printing SMT script: " + e); //$NON-NLS-1$
//                                }
//                            }
                            try {
                                solverResponse = script.execute(solver2); // Note - the solver knows the smt configuration
                            } catch (Exception e) {
                                // Not sure there is anything to worry about, but just in case
                                //log.error("jml.esc.badscript", methodDecl.getName(), e.toString()); //$NON-NLS-1$
                                JCDiagnostic d = log.factory().error(log.currentSource(), null, "jml.esc.badscript", methodDecl.getName(), e.toString());
                                log.report(d);
                                return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start).setOtherInfo(d);
                            } finally {
                                solver2.exit();
                                solver2 = null;
                            }
                           
                        }
                        if (usePushPop) {
                            solver.pop(1); // Pop off previous setting of assumeCheck
                            solver.push(1); // Mark the top
                            JCExpression bin = treeutils.makeBinary(Position.NOPOS,JCTree.Tag.EQ,treeutils.inteqSymbol,
                                    treeutils.makeIdent(Position.NOPOS,jmlesc.assertionAdder.assumeCheckSym),
                                    treeutils.makeIntLiteral(Position.NOPOS, feasibilityCheckNumber));
                            solver.assertExpr(smttrans.convertExpr(bin));
                            solverResponse = solver.check_sat();
                        }
                        String description = stat.description; // + " " + stat;
                        String fileLocation = utils.locationString(stat.pos, log.currentSourceFile());
                        String msg =  (utils.jmlverbose >= Utils.PROGRESS) ? 
                                ("Feasibility check #" + feasibilityCheckNumber + " - " + description + " : ")
                                :("Feasibility check - " + description + " : ");
                        boolean infeasible = solverResponse.equals(unsatResponse);
                        if (Utils.testingMode) fileLocation = loc;
                        utils.progress(0,1,fileLocation + msg + (infeasible ? "infeasible": "OK"));
                        if (infeasible) {
                            if (Strings.preconditionAssumeCheckDescription.equals(description)) {
                                log.warning(stat.pos(), "esc.infeasible.preconditions", utils.qualifiedMethodSig(methodDecl.sym));
                                proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.INFEASIBLE,start);
                                // If the preconditions are inconsistent, all paths will be infeasible
                                break;
                            } else {
                                log.warning(stat.pos(), "esc.infeasible.assumption", description, utils.qualifiedMethodSig(methodDecl.sym));
                                if (Strings.feasibilityContains(stat.description,context)) proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.INFEASIBLE,start);
                            }
                        } else if (solverResponse.isError()) {
                            if (usePushPop) solver.exit();
                            //log.error("jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                            JCDiagnostic d = log.factory().error(log.currentSource(), null, "jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse));
                            log.report(d);
                            return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start).setOtherInfo(d);
                        }
                        // FIXME - what about timeout?
                    }
                }
            } else b: { // Proof was not UNSAT, so there may be a counterexample
                if (!Utils.testingMode) utils.progress(0,1,loc + " Method assertions are INVALID");
                int count = Utils.instance(context).maxWarnings;
                boolean byPath = JmlOption.isOption(context, JmlOption.MAXWARNINGSPATH);
                ProverResult pr = (ProverResult)factory.makeProverResult(methodDecl.sym,proverToUse,
                        solverResponse.toString().equals("sat") ? IProverResult.SAT : IProverResult.POSSIBLY_SAT,start);
                proofResult = pr;
                boolean haveFailedAssertion = false;
                while (prevErrors == log.nerrors) {
                    if (aborted) {
                    	throw new Main.JmlCanceledException("Aborted by user");
                    }

                    if (solverResponse.isError()) {
                        solver.exit();
                        //log.error("jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                        JCDiagnostic d = log.factory().error(log.currentSource(), null, "jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse));
                        log.report(d);
                        return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start).setOtherInfo(d);
                    }
                    if (solverResponse.equals(smt.smtConfig.responseFactory.unknown())) {
                        IResponse unknownReason = solver.get_info(smt.smtConfig.exprFactory.keyword(":reason-unknown")); // Not widely supported
                        if (unknownReason.equals(smt.smtConfig.responseFactory.unsupported())) {
                            // continue
                        } else if (unknownReason instanceof IResponse.IAttributeList) {
                            IResponse.IAttributeList attrList = (IResponse.IAttributeList)unknownReason;
                            IAttributeValue value = attrList.attributes().get(0).attrValue();
                            if (value.toString().contains("incomplete")) { // FIXME - this might be only CVC4
                                // continue on
                            } else if (value.toString().equals("ok")) { // FIXME - this might be only Z3
                                    // continue on
                            } else {
                                String msg = "Aborted proof: " + smt.smtConfig.defaultPrinter.toString(value);
                                unknownReason = smt.smtConfig.responseFactory.error(msg);
                                boolean timeout = msg.contains("timeout");
                                if (timeout) {
                                	log.warning(methodDecl,"esc.resourceout",": " + msg);
                                	if (!haveFailedAssertion) proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.TIMEOUT,start);
                                    break b;
                                }
                            }
                        } else {
                            // Unexpected result
                            log.error("jml.internal.notsobad","Unexpected result when querying SMT solver for reason for an unknown result: " + unknownReason);
                            break b;
                        }
                        
                        // Instead, try to get a simple value and see if there is a model
                        IResponse r = solver.get_value(smt.smtConfig.exprFactory.symbol("NULL"));
                        if (r.isError()) {
                            String msg = ": ";
                            if (JmlOption.value(context,JmlOption.TIMEOUT) != null) msg = " (possible timeout): ";
                            log.warning(methodDecl,"esc.nomodel","method " + utils.qualifiedName(methodDecl.sym) + " - " + msg + r);
                            if (!haveFailedAssertion) proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNKNOWN,start);
                            break b;
                        }

                    }
                    
                    // If we don't clearly know the prover failed, we try to get a simple value and see if there is a model
                    IResponse r = solver.get_value(smt.smtConfig.exprFactory.symbol("NULL"));
                    if (r.isError()) {
                        String msg = ": ";
                        if (JmlOption.value(context,JmlOption.TIMEOUT) != null) msg = " (possible timeout): ";
                        log.warning(methodDecl,"esc.nomodel",msg + r);
                        if (!haveFailedAssertion) proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNKNOWN,start);
                        break b;
                    }


                    if (print) log.getWriter(WriterKind.NOTICE).println("Some assertion is not valid");
                    haveFailedAssertion = true;
                    
                    // FIXME - decide how to show counterexamples when there is no tracing
                    Map<JCTree,String> cemap = constructCounterexample(jmlesc.assertionAdder,basicBlocker,smttrans,smt,solver);
                    BiMap<JCTree,JCExpression> jmap = jmlesc.assertionAdder.exprBiMap.compose(basicBlocker.bimap);
                    tracer = tracerFactory.makeTracer(context,smt,solver,cemap,jmap);

                    // Report JML-labeled values and the path to the failed invariant
                    {
                        tracer.appendln(JmlTree.eol + "TRACE of " + utils.qualifiedMethodSig(methodDecl.sym));
                        if (utils.jmlverbose  >= Utils.JMLVERBOSE) tracer.appendln("Constants");
                        populateConstantMap(smt, solver, cemap, smttrans);
                    }
                    path = new ArrayList<IProverResult.Span>();
                    JCExpression pathCondition = reportInvalidAssertion(
                            program,smt,solver,methodDecl,cemap,jmap,
                            jmlesc.assertionAdder.pathMap, basicBlocker.pathmap);
                    
                    if (showTrace) log.getWriter(WriterKind.NOTICE).println(tracer.text());

                    // FIXME - decide how to show counterexamples when there is no tracing
                    if (showCounterexample) {
                        log.getWriter(WriterKind.NOTICE).println("\nCOUNTEREXAMPLE");
                        for (VarSymbol v: basicBlocker.premap.keySet()) {
                            Name n = basicBlocker.premap.getName(v);
                            String ns = n.toString();
                            if (ns.equals("this")) continue; // FIXME - use symbols for these
                            if (ns.equals("length")) continue;
                            if (ns.equals("_alloc__")) continue;
                            if (ns.equals("_heap__")) continue;

                            String s = getValue(n.toString(),smt,solver);
                            log.getWriter(WriterKind.NOTICE).println(n.toString() + " = " + s);
                        }
                        log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                    }
                    

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
                        //log.error("jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                        JCDiagnostic d = log.factory().error(log.currentSource(), null, "jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse));
                        log.report(d);
                        return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start).setOtherInfo(d);
                    }
                    if (solverResponse.equals(unsatResponse)) break;
                    // TODO -  checking each assertion separately
                }
                //pr.accumulateDuration((new Date().getTime() - pr.timestamp().getTime())/1000.);
            }
        }
        if (usePushPop) {
            solver.exit();
            solver = null;
        }
        smt.smtConfig.logfile = null;
//        saveBenchmark(proverToUse,methodDecl.name.toString());
//        jmlesc.mostRecentProgram = program;
        if (prevErrors != log.nerrors) {
            // FIXME - include information about the errors - now just in UI
            return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start);
        }
        return proofResult;
        
    }
    
    protected List<IProverResult.Span> path;


    public void populateConstantMap(SMT smt, ISolver solver, Map<JCTree,String> cemap,
            SMTTranslator smttrans) {
        addToConstantMap(smttrans.NULL,smt,solver,cemap);
        addToConstantMap(smttrans.thisSym.toString(),smt,solver,cemap);
//        for (Type t : smttrans.javaTypes) {
//            String s = smttrans.javaTypeSymbol(t).toString(); // FIXME - need official printer
//            addToConstantMap(s,smt,solver,cemap);
//            s = smttrans.jmlTypeSymbol(t).toString(); // FIXME - need official printer
//            addToConstantMap(s,smt,solver,cemap);
//        }
    }
    
    public void addToConstantMap(String id, SMT smt, ISolver solver, Map<JCTree,String> cemap) {
        String result = getValue(id,smt,solver);
        if (result != null && result.startsWith("#x")) {
            try {
                Long v = Long.valueOf(result.substring(2),16);
                result = result + " (" + v + ")";
            } catch (NumberFormatException e) {
                // Just skip - don't try to add additional information
            }
        }
        if (result != null) constantTraceMap.put(result,id);
        if (utils.jmlverbose  >= Utils.JMLVERBOSE) {
            tracer.appendln("\t\t\tVALUE: " + id + "\t === " + 
                    result);
        }

    }
    
    public void addToConstantMap(JCExpression e, Map<JCTree,String> cemap, SMTTranslator smttrans) {
        String result = cemap.get(e);
        String expr = smttrans.convertExpr(e).toString();// TODO - use the pretty printer?
        if (result != null) constantTraceMap.put(result,e.toString()); 
        if (e.type.getTag() == TypeTag.CHAR) result = showChar(result); 
        if (utils.jmlverbose  >= Utils.JMLVERBOSE) tracer.appendln("\t\t\tVALUE: " + expr + "\t === " + 
                 result);

    }
    
    public static class Info {
        public boolean verbose;
        public SMT smt;
        public ISolver solver;
        public JCMethodDecl decl;
        public Map<JCTree,String> cemap;
        public BiMap<JCTree,JCExpression> jmap;
        public BiMap<JCTree,JCTree> aaPathMap;
        public BiMap<JCTree,JCTree> bbPathMap;
    }
    
    /** Iterates through the basic blocks to find and report the invalid assertion
     * that caused the SAT result from the prover. The pathCondition that is returned is
     * the negation of the conjunction of the block conditions on the path leading to the false assertion;
     * that is, if the returned expression is assumed, the false assertion will
     * not be reachable, so another invalid assertion may be found.
     */
    public JCExpression reportInvalidAssertion(BasicProgram program, SMT smt, ISolver solver, JCMethodDecl decl,
            Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap,
            BiMap<JCTree,JCTree> aaPathMap, BiMap<JCTree,JCTree> bbPathMap) {
        Info info = new Info();
        info.verbose = utils.jmlverbose >= Utils.JMLVERBOSE;
        info.smt = smt;
        info.solver = solver;
        info.decl = decl;
        info.cemap = cemap;
        info.jmap = jmap;
        info.aaPathMap = aaPathMap;
        info.bbPathMap = bbPathMap;
        JCExpression pathCondition = reportInvalidAssertion2(program.startBlock(),info,0, JmlTreeUtils.instance(context).falseLit);
        if (pathCondition == null) {
            log.warning("jml.internal.notsobad","Could not find an invalid assertion even though the proof result was satisfiable: " + decl.sym); //$NON-NLS-1$ //$NON-NLS-2$
            return null;
        }
        return pathCondition;
    }
    
    public JCExpression reportInvalidAssertion2(BasicProgram.BasicBlock sblock, Info info, int sterminationPos, JCExpression spathCondition) {
        // On large problems (or even moderate ones) we can overflow the stack searching the block DAG.
        // So instead we make it iterative with a few state stacks
        
        Stack<BasicProgram.BasicBlock> blockStack = new Stack<>();
        Stack<Integer> terminationStack = new Stack<>();
        Stack<JCExpression> pathConditionStack = new Stack<>();
        blockStack.push(sblock);
        terminationStack.push(sterminationPos);
        pathConditionStack.push(spathCondition);
        
        while (!blockStack.isEmpty()) {
            BasicProgram.BasicBlock block = blockStack.pop();
            int terminationPos = terminationStack.pop();
            JCExpression pathCondition = pathConditionStack.pop();
            
            String id = block.id.name.toString();
            Boolean value = getBoolValue(id,info.smt,info.solver);
            if (value == null) {
                log.warning("jml.messsage", "Failed to obtain a block value " + id);
                // FIXME - error and what to do ?
                continue;
            }
            if (info.verbose && (JmlOption.isOption(context,JmlOption.COUNTEREXAMPLE) || JmlOption.isOption(context,JmlOption.SUBEXPRESSIONS))) {
                tracer.appendln("Block " + id + " is " + value);  //$NON-NLS-1$//$NON-NLS-2$
            }
            if (value) {
                // The value of the block id is true, so we don't pursue it
                continue;
            }
            terminationPos = checkTerminationPosition(id,terminationPos);
            //showTrace = true;
            // FIXME - would like to have a range, not just a single position point,
            // for the terminationPos
            for (JCStatement stat: block.statements()) {
                // Report any statements that are JML-labels
                if (stat instanceof JCVariableDecl) {
                    Name n = ((JCVariableDecl)stat).name;
                    String ns = n.toString();
                    if (ns.startsWith(Strings.labelVarString)) {
                        JavaFileObject prev = log.useSource( ((JmlVariableDecl)stat).sourcefile );
                        int k = ns.lastIndexOf(Strings.underscore);
                        if (ns.startsWith(prefix_lblpos)) {
                            Boolean b = getBoolValue(ns,info.smt,info.solver);
                            String label = ns.substring(prefix_lblpos.length(),k); 
                            if (b == null) log.warning(stat.pos,"esc.label.value",label,"is unknown"); //$NON-NLS-1$
                            else if (b) log.warning(stat.pos,"esc.label.value",label,b); //$NON-NLS-1$
                        } else if (ns.startsWith(prefix_lblneg)) {
                            Boolean b = getBoolValue(ns,info.smt,info.solver);
                            String label = ns.substring(prefix_lblneg.length(),k); 
                            if (b == null) log.warning(stat.pos,"esc.label.value",label,"is unknown"); //$NON-NLS-1$
                            else if (!b) log.warning(stat.pos,"esc.label.value",label,b); //$NON-NLS-1$
                        } else if (ns.startsWith(prefix_lbl)) {
                            String b = getValue(ns,info.smt,info.solver);
                            String label = ns.substring(prefix_lbl.length(),k); 
                            JCExpression eshow = jmlesc.assertionAdder.showExpressions.get(label);
                            if (b == null) log.warning(stat.pos,"esc.label.value",label,"is unknown"); //$NON-NLS-1$
                            else if (eshow == null) log.warning(stat.pos,"esc.label.value",label,b); //$NON-NLS-1$
                            else log.warning(stat.pos,"esc.label.expr",eshow.toString(),b);
                        } else {
                            log.warning(stat.pos,"jml.internal.notsobad","Unknown label: " + ns); //$NON-NLS-1$
                        }
                        log.useSource(prev);
                    }
                }
                
                {
                    JCStatement bbstat = stat;
                    JCTree origStat = info.aaPathMap.getr(bbstat);
                    String comment = bbstat instanceof JmlStatementExpr &&
                            ((JmlStatementExpr)bbstat).expression instanceof JCLiteral ?
                                    ((JCLiteral)((JmlStatementExpr)bbstat).expression).value.toString()
                                    : null;
                    ifstat: if (origStat != null || stat instanceof JmlStatementExpr){
                        String loc = origStat == null ? "" :utils.locationString(origStat.getStartPosition());
                        //String comment = ((JCLiteral)((JmlStatementExpr)bbstat).expression).value.toString();
                        int sp=-2,ep=-2; // The -2 is different from NOPOS and (presumably) any other value that might be generated below
                        int spanType = Span.NORMAL;
                        JCTree toTrace = null;
                        String val = null;
                        if (origStat instanceof JmlStatementExpr && ((JmlStatementExpr)origStat).token == JmlTokenKind.ASSUME) {
                            //toTrace = ((JmlStatementExpr)stat).expression;
                            break ifstat;
                        } else if (origStat instanceof JCIf) {
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
//                        } else if (origStat instanceof JmlEnhancedForLoop) {
//                            JmlEnhancedForLoop s = (JmlEnhancedForLoop)origStat;
//                            sp = s.getCondition().getStartPosition();
//                            ep = s.getCondition().getEndPosition(log.currentSource().getEndPosTable());
                        } else if (origStat instanceof JmlVariableDecl) {
                            JmlVariableDecl s = (JmlVariableDecl)origStat;
                            sp = s.getStartPosition();
                            ep = s.getEndPosition(log.currentSource().getEndPosTable());
                            toTrace = s.ident;
                            tracer.appendln(loc + " \t" + comment);
                            if (toTrace != null && showSubexpressions) tracer.trace(s.init);
                            if (toTrace != null && showSubexpressions) tracer.trace(s.ident);
                            break ifstat;
//                        } else if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlTokenKind.COMMENT && ((JmlStatementExpr)stat).expression.toString().contains("ImplicitAssume")) {
//                            break ifstat;
                        } else {
                            toTrace = origStat;
                        }
                        if (toTrace != null && sp == -2) {
                            sp = toTrace.getStartPosition();
                            ep = toTrace.getEndPosition(log.currentSource().getEndPosTable());
                            val = info.cemap.get(toTrace);
                            spanType = val == null ? Span.NORMAL : val.equals("true") ? Span.TRUE : Span.FALSE;
                        }
                        //log.getWriter(WriterKind.NOTICE).println("SPAN " + sp + " " + ep + " " + spanType);
                        if (sp > Position.NOPOS) { // Neither -2 nor NOPOS
                            if (ep >= sp) path.add(new Span(sp,ep,spanType));
//                            else log.warning(Position.NOPOS,"jml.internal.notsobad","Incomplete position information (" + sp + " " + ep + ") for " + origStat);
                        } else {
//                            log.warning(Position.NOPOS,"jml.internal.notsobad","Incomplete position information (" + sp + " " + ep + ") for " + origStat);
                        }
                        if (comment != null) {
                            if (comment.startsWith("AssumeCheck assertion")) break ifstat;
                            if (info.verbose || toTrace != null) tracer.appendln(loc + " \t" + comment);
                        }
                        if (toTrace != null && showSubexpressions) tracer.trace(toTrace);
                        String s = ((JmlStatementExpr)bbstat).id;
                        if (toTrace != null && s != null) {
                            tracer.appendln("\t\t\t\t" + s + " = " + info.cemap.get(toTrace));
                        }
                        
                    } else if (info.aaPathMap.reverse.keySet().contains(bbstat)) {
                        String loc = utils.locationString(bbstat.getStartPosition());
                        //String comment = ((JCLiteral)((JmlStatementExpr)bbstat).expression).value.toString();
                        tracer.appendln(loc + " \t" + comment);
                    } else if (comment != null) {
                        tracer.appendln(" \t//" + comment);
                    }
                }
                
                if (showBBTrace) {
                    log.getWriter(WriterKind.NOTICE).println("STATEMENT: " + stat);
                    if (stat instanceof JmlStatementExpr) {
                        JmlStatementExpr x = (JmlStatementExpr)stat;
                        tracer.trace(x.expression);
                        log.getWriter(WriterKind.NOTICE).println(tracer.text());
                        tracer.clear();
                    } else if (stat instanceof JCVariableDecl) {
                        JCVariableDecl vd = (JCVariableDecl)stat;
                        Name n = vd.name;
                        if (vd.init != null) tracer.trace(vd.init);
                        log.getWriter(WriterKind.NOTICE).println("DECL: " + n + " === " + getValue(n.toString(),info.smt,info.solver));
                    }
                }
                if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlTokenKind.COMMENT) {
                    JmlStatementExpr s = (JmlStatementExpr)stat;
                    if (s.id == null || !s.id.startsWith("ACHECK")) continue;
                    if (s.optionalExpression != null) {
                        log.getWriter(WriterKind.NOTICE).println("FOUND " + s.id);
                        return pathCondition;
                    }
                }
                if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlTokenKind.ASSERT) {
                    JmlStatementExpr assertStat = (JmlStatementExpr)stat;
                    JCExpression e = assertStat.expression;
                    Label label = assertStat.label;
                    if (e instanceof JCTree.JCLiteral) {
                        value = ((JCTree.JCLiteral)e).value.equals(1); // Boolean literals have 0 and 1 value
                    } else if (e instanceof JCTree.JCParens) {
                        value = ((JCTree.JCLiteral)((JCTree.JCParens)e).expr).value.equals(1); // Boolean literals have 0 and 1 value
                    } else if (e instanceof JCIdent){
                        id = e.toString(); // Relies on all assert statements being reduced to identifiers
                        value = getBoolValue(id,info.smt,info.solver);
                    } else {
                        return pathCondition; // For when assert statements are not identifiers
                    }
                    if (!value) { 
                        boolean byPath = JmlOption.isOption(context, JmlOption.MAXWARNINGSPATH);
                        if (byPath) pathCondition = JmlTreeUtils.instance(context).makeOr(Position.NOPOS, pathCondition, e);
                        else pathCondition = e;
                        if (terminationPos == 0) terminationPos = info.decl.pos;

                        JavaFileObject prev = null;
                        int pos = assertStat.pos;
                        if (pos == Position.NOPOS || pos == info.decl.pos) {
                            pos = terminationPos;
                            prev = log.useSource(((JmlMethodDecl)info.decl).sourcefile);
                        } else {
                            if (assertStat.source != null) prev = log.useSource(assertStat.source);
                        }
                        JavaFileObject mainSource = log.currentSourceFile();
                        String associatedLocation = Strings.empty;
                        if (assertStat.associatedPos != Position.NOPOS && !Utils.testingMode) {
                            associatedLocation = ": " + utils.locationString(assertStat.associatedPos,assertStat.associatedSource); 
                        }
                        String extra = Strings.empty;
                        JCExpression optional = assertStat.optionalExpression;
                        if (optional != null) {
                            if (optional instanceof JCTree.JCLiteral) extra = ": " + ((JCTree.JCLiteral)optional).getValue().toString(); //$NON-NLS-1$
                        }
                        if (assertStat.description != null && label != Label.PRECONDITION && label != Label.UNDEFINED_PRECONDITION) {
                            extra = ": " + assertStat.description;
                        }
                        
                        if (JmlOption.includes(context, JmlOption.SHOW,"translated")) log.getWriter(WriterKind.NOTICE).println("Failed assert: " + e.toString());
                        int epos = assertStat.getEndPosition(log.currentSource().getEndPosTable());
                        String loc;
                        if (epos == Position.NOPOS || pos != assertStat.pos) {
                            log.warning(pos,"esc.assertion.invalid",label,associatedLocation,utils.methodName(info.decl.sym),extra); //$NON-NLS-1$
                            loc = utils.locationString(pos);
                            tracer.appendln(loc + " Invalid assertion (" + label + ")");
                        } else {
                            // FIXME - migrate to using pos() for terminationPos as well 
                            log.warning(assertStat.getPreferredPosition(),"esc.assertion.invalid",label,associatedLocation,utils.methodName(info.decl.sym),extra); //$NON-NLS-1$
                            loc = utils.locationString(assertStat.getPreferredPosition());
                            tracer.appendln(loc + " Invalid assertion (" + label + ")");
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
                            tracer.appendln(associatedLocation + " Associated location");
                            if (assertStat.associatedSource != null) log.useSource(prev);
                        }
                        if (assertStat.associatedClause != null && JmlOption.isOption(context,JmlOption.ESC_EXIT_INFO)) {
                            JmlTokenKind tkind = assertStat.associatedClause.token;
                            if (tkind == JmlTokenKind.ENSURES || tkind == JmlTokenKind.SIGNALS || tkind == JmlTokenKind.SIGNALS_ONLY) {  // FIXME - actually - any postcondition check
                                int p = terminationPos;
                                if (p != pos || !mainSource.getName().equals(assertStat.source.getName())) {
                                    if (terminationPos == info.decl.pos) p = info.decl.getEndPosition(log.getSource(mainSource).getEndPosTable());
                                    JavaFileObject prevv = log.useSource(mainSource);
                                    if (p != Position.NOPOS) log.warning(p, "jml.message", "Associated method exit");
                                    log.useSource(prevv);
                                }
                            }
                        }

                        if (label == Label.PRECONDITION || label == Label.UNDEFINED_PRECONDITION) {
                            //BiMap<JCTree,JCTree> bimap = jmlesc.assertionAdder.exprBiMap;
                            //for (int pdetail=1; pdetail <= jmlesc.assertionAdder.preconditionDetail; pdetail++) 
                            {
                               String nm = assertStat.description;
                               //logPreValue(nm,cemap);
                               Boolean v = findPreValue(nm,info.cemap);
                                //log.note("jml.message",nm + " " + v);
                               if (v != null && !v) {
                                    int pdetail2 = 0;
                                    while (true) {
                                        pdetail2++;
                                        String nmm = nm + "_" + pdetail2;
                                        Boolean vv = findPreValue(nmm,info.cemap);
                                        //log.note("jml.message",nmm + " " + vv);
                                        if (vv == null && pdetail2 > 6) break;
                                        if (true || !vv) {
                                            int pdetail3 = 0;
                                            while (true) {
                                                pdetail3++;
                                                String nmmm = nmm + "_" + pdetail3;
                                                Boolean vvv = findPreValue(nmmm,info.cemap);
                                                //log.note("jml.message",nmmm + " " + vvv);
                                                if (vvv == null) break;
                                                if (!vvv) {
                                                    JCTree s = findPreExpr(nmmm,info.cemap);
                                                    JavaFileObject prevv = log.useSource(jmlesc.assertionAdder.preconditionDetailClauses.get(nmmm));
                                                    log.warning(s.pos,"esc.false.precondition.conjunct", s.toString());
                                                    log.useSource(prevv);
                                                    break;
                                                } else {
                                                    continue;
                                                }
                                            }
                                        } else {
                                            // FIXME - there cannot be a true value here
                                        }
                                    }
                                }
                            }
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
                blockStack.push(b);
                terminationStack.push(terminationPos);
                pathConditionStack.push(pathCondition);
            }
        }
        
        
        return null;
    }
    
    // These strings must mirror the strings used in JmlAsssertionAdder.visitJmlLblExpression
    private final static String prefix_lblpos = Strings.labelVarString + JmlTokenKind.BSLBLPOS.internedName().substring(1) + "_";
    private final static String prefix_lblneg = Strings.labelVarString + JmlTokenKind.BSLBLNEG.internedName().substring(1) + "_";
    private final static String prefix_lbl = Strings.labelVarString + JmlTokenKind.BSLBLANY.internedName().substring(1) + "_";

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
     * Returns non-null if an invalid assertion was found and reported.
     * The terminationPos is the value of terminationPos found so far; it is used
     * in the report of invalid postconditions to say which exit path results in
     * the false postcondition.
     */
    // How this works: If there is an invalid assertion, then the value of the blockid
    // of the block containing that assertion is false; recursively, the blockid
    // is false for any block that has a following block with a false blockid.
    // Thus if there is an invalid assertion the start block is false and there is
    // a path of false blocks to the invalid assertion. There could possibly be
    // other blocks with false ids as well.
    public JCExpression reportInvalidAssertion(BasicProgram.BasicBlock block, Info info, int terminationPos, JCExpression pathCondition) {
        String id = block.id.name.toString();
        Boolean value = getBoolValue(id,info.smt,info.solver);
        if (value == null) {
            // FIXME - error and what to do ?
            return null;
        }
        if (info.verbose && (JmlOption.isOption(context,JmlOption.COUNTEREXAMPLE) || JmlOption.isOption(context,JmlOption.SUBEXPRESSIONS))) {
            tracer.appendln("Block " + id + " is " + value);  //$NON-NLS-1$//$NON-NLS-2$
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
            // Report any statements that are JML-labels
            if (stat instanceof JCVariableDecl) {
                Name n = ((JCVariableDecl)stat).name;
                String ns = n.toString();
                if (ns.startsWith(Strings.labelVarString)) {
                    JavaFileObject prev = log.useSource( ((JmlVariableDecl)stat).sourcefile );
                    int k = ns.lastIndexOf(Strings.underscore);
                    if (ns.startsWith(prefix_lblpos)) {
                        Boolean b = getBoolValue(ns,info.smt,info.solver);
                        String label = ns.substring(prefix_lblpos.length(),k); 
                        if (b == null) log.warning(stat.pos,"esc.label.value",label,"is unknown"); //$NON-NLS-1$
                        else if (b) log.warning(stat.pos,"esc.label.value",label,b); //$NON-NLS-1$
                    } else if (ns.startsWith(prefix_lblneg)) {
                        Boolean b = getBoolValue(ns,info.smt,info.solver);
                        String label = ns.substring(prefix_lblneg.length(),k); 
                        if (b == null) log.warning(stat.pos,"esc.label.value",label,"is unknown"); //$NON-NLS-1$
                        else if (!b) log.warning(stat.pos,"esc.label.value",label,b); //$NON-NLS-1$
                    } else if (ns.startsWith(prefix_lbl)) {
                        String b = getValue(ns,info.smt,info.solver);
                        String label = ns.substring(prefix_lbl.length(),k); 
                        JCExpression eshow = jmlesc.assertionAdder.showExpressions.get(label);
                        System.out.println(label + " " + eshow);
                        if (b == null) log.warning(stat.pos,"esc.label.value",label,"is unknown"); //$NON-NLS-1$
                        else if (eshow == null) log.warning(stat.pos,"esc.label.value",label,b); //$NON-NLS-1$
                        else log.warning(stat.pos,"esc.label.value",eshow.toString(),b);
                    } else {
                        log.warning(stat.pos,"jml.internal.notsobad","Unknown label: " + ns); //$NON-NLS-1$
                    }
                    log.useSource(prev);
                }
            }
            
            {
                JCStatement bbstat = stat;
                JCTree origStat = info.aaPathMap.getr(bbstat);
                String comment = bbstat instanceof JmlStatementExpr &&
                        ((JmlStatementExpr)bbstat).expression instanceof JCLiteral ?
                                ((JCLiteral)((JmlStatementExpr)bbstat).expression).value.toString()
                                : null;
                ifstat: if (origStat != null || stat instanceof JmlStatementExpr){
                    String loc = origStat == null ? "" :utils.locationString(origStat.getStartPosition());
                    //String comment = ((JCLiteral)((JmlStatementExpr)bbstat).expression).value.toString();
                    int sp=-2,ep=-2; // The -2 is different from NOPOS and (presumably) any other value that might be generated below
                    int spanType = Span.NORMAL;
                    JCTree toTrace = null;
                    String val = null;
                    if (origStat instanceof JmlStatementExpr && ((JmlStatementExpr)origStat).token == JmlTokenKind.ASSUME) {
                        //toTrace = ((JmlStatementExpr)stat).expression;
                        break ifstat;
                    } else if (origStat instanceof JCIf) {
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
                        if (toTrace != null && showSubexpressions) tracer.trace(s.init);
                        if (toTrace != null && showSubexpressions) tracer.trace(s.ident);
                        break ifstat;
//                    } else if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlTokenKind.COMMENT && ((JmlStatementExpr)stat).expression.toString().contains("ImplicitAssume")) {
//                        break ifstat;
                    } else {
                        toTrace = origStat;
                    }
                    if (toTrace != null && sp == -2) {
                        sp = toTrace.getStartPosition();
                        ep = toTrace.getEndPosition(log.currentSource().getEndPosTable());
                        val = info.cemap.get(toTrace);
                        spanType = val == null ? Span.NORMAL : val.equals("true") ? Span.TRUE : Span.FALSE;
                    }
                    //log.getWriter(WriterKind.NOTICE).println("SPAN " + sp + " " + ep + " " + spanType);
                    if (sp > Position.NOPOS) { // Neither -2 nor NOPOS
                        if (ep >= sp) path.add(new Span(sp,ep,spanType));
//                        else log.warning(Position.NOPOS,"jml.internal.notsobad","Incomplete position information (" + sp + " " + ep + ") for " + origStat);
                    } else {
//                        log.warning(Position.NOPOS,"jml.internal.notsobad","Incomplete position information (" + sp + " " + ep + ") for " + origStat);
                    }
                    if (comment != null) {
                        if (comment.startsWith("AssumeCheck assertion")) break ifstat;
                        if (info.verbose || toTrace != null) tracer.appendln(loc + " \t" + comment);
                    }
                    if (toTrace != null && showSubexpressions) tracer.trace(toTrace);
                    String s = ((JmlStatementExpr)bbstat).id;
                    if (toTrace != null && s != null) {
                        tracer.appendln("\t\t\t\t" + s + " = " + info.cemap.get(toTrace));
                    }
                    
                } else if (info.aaPathMap.reverse.keySet().contains(bbstat)) {
                    String loc = utils.locationString(bbstat.getStartPosition());
                    //String comment = ((JCLiteral)((JmlStatementExpr)bbstat).expression).value.toString();
                    tracer.appendln(loc + " \t" + comment);
                } else if (comment != null) {
                    tracer.appendln(" \t//" + comment);
                }
            }
            
            if (showBBTrace) {
                log.getWriter(WriterKind.NOTICE).println("STATEMENT: " + stat);
                if (stat instanceof JmlStatementExpr) {
                    JmlStatementExpr x = (JmlStatementExpr)stat;
                    tracer.trace(x.expression);
                    log.getWriter(WriterKind.NOTICE).println(tracer.text());
                    tracer.clear();
                } else if (stat instanceof JCVariableDecl) {
                    JCVariableDecl vd = (JCVariableDecl)stat;
                    Name n = vd.name;
                    if (vd.init != null) tracer.trace(vd.init);
                    log.getWriter(WriterKind.NOTICE).println("DECL: " + n + " === " + getValue(n.toString(),info.smt,info.solver));
                }
            }
            if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlTokenKind.COMMENT) {
                JmlStatementExpr s = (JmlStatementExpr)stat;
                if (s.id == null || !s.id.startsWith("ACHECK")) continue;
                if (s.optionalExpression != null) {
                    log.getWriter(WriterKind.NOTICE).println("FOUND " + s.id);
                    return pathCondition;
                }
            }
            if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlTokenKind.ASSERT) {
                JmlStatementExpr assertStat = (JmlStatementExpr)stat;
                JCExpression e = assertStat.expression;
                Label label = assertStat.label;
                if (e instanceof JCTree.JCLiteral) {
                    value = ((JCTree.JCLiteral)e).value.equals(1); // Boolean literals have 0 and 1 value
                } else if (e instanceof JCTree.JCParens) {
                    value = ((JCTree.JCLiteral)((JCTree.JCParens)e).expr).value.equals(1); // Boolean literals have 0 and 1 value
                } else if (e instanceof JCIdent){
                    id = e.toString(); // Relies on all assert statements being reduced to identifiers
                    value = getBoolValue(id,info.smt,info.solver);
                } else {
                    return pathCondition; // For when assert statements are not identifiers
                }
                if (!value) { 
                    boolean byPath = JmlOption.isOption(context, JmlOption.MAXWARNINGSPATH);
                    if (byPath) pathCondition = JmlTreeUtils.instance(context).makeOr(Position.NOPOS, pathCondition, e);
                    else pathCondition = e;
                    if (terminationPos == 0) terminationPos = info.decl.pos;

                    JavaFileObject prev = null;
                    int pos = assertStat.pos;
                    if (pos == Position.NOPOS || pos == info.decl.pos) {
                        pos = terminationPos;
                        prev = log.useSource(((JmlMethodDecl)info.decl).sourcefile);
                    } else {
                        if (assertStat.source != null) prev = log.useSource(assertStat.source);
                    }
                    JavaFileObject mainSource = log.currentSourceFile();
                    String associatedLocation = Strings.empty;
                    if (assertStat.associatedPos != Position.NOPOS && !Utils.testingMode) {
                        associatedLocation = ": " + utils.locationString(assertStat.associatedPos,assertStat.associatedSource); 
                    }
                    String extra = Strings.empty;
                    JCExpression optional = assertStat.optionalExpression;
                    if (optional != null) {
                        if (optional instanceof JCTree.JCLiteral) extra = ": " + ((JCTree.JCLiteral)optional).getValue().toString(); //$NON-NLS-1$
                    }
                    if (assertStat.description != null && label != Label.PRECONDITION && label != Label.UNDEFINED_PRECONDITION) {
                        extra = ": " + assertStat.description;
                    }
                    
                    if (JmlOption.includes(context, JmlOption.SHOW, "translated")) log.getWriter(WriterKind.NOTICE).println("Failed assert: " + e.toString());
                    int epos = assertStat.getEndPosition(log.currentSource().getEndPosTable());
                    String loc;
                    if (epos == Position.NOPOS || pos != assertStat.pos) {
                        log.warning(pos,"esc.assertion.invalid",label,associatedLocation,utils.methodName(info.decl.sym),extra); //$NON-NLS-1$
                        loc = utils.locationString(pos);
                        tracer.appendln(loc + " Invalid assertion (" + label + ")");
                    } else {
                        // FIXME - migrate to using pos() for terminationPos as well 
                        log.warning(assertStat.getPreferredPosition(),"esc.assertion.invalid",label,associatedLocation,utils.methodName(info.decl.sym),extra); //$NON-NLS-1$
                        loc = utils.locationString(assertStat.getPreferredPosition());
                        tracer.appendln(loc + " Invalid assertion (" + label + ")");
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
                        tracer.appendln(associatedLocation + " Associated location");
                        if (assertStat.associatedSource != null) log.useSource(prev);
                    }
                    if (assertStat.associatedClause != null && JmlOption.isOption(context,JmlOption.ESC_EXIT_INFO)) {
                        JmlTokenKind tkind = assertStat.associatedClause.token;
                        if (tkind == JmlTokenKind.ENSURES || tkind == JmlTokenKind.SIGNALS || tkind == JmlTokenKind.SIGNALS_ONLY) {  // FIXME - actually - any postcondition check
                            int p = terminationPos;
                            if (p != pos || !mainSource.getName().equals(assertStat.source.getName())) {
                                if (terminationPos == info.decl.pos) p = info.decl.getEndPosition(log.getSource(mainSource).getEndPosTable());
                                JavaFileObject prevv = log.useSource(mainSource);
                                if (p != Position.NOPOS) log.warning(p, "jml.message", "Associated method exit");
                                log.useSource(prevv);
                            }
                        }
                    }

                    if (label == Label.PRECONDITION || label == Label.UNDEFINED_PRECONDITION) {
                        //BiMap<JCTree,JCTree> bimap = jmlesc.assertionAdder.exprBiMap;
                        //for (int pdetail=1; pdetail <= jmlesc.assertionAdder.preconditionDetail; pdetail++) 
                        {
                           String nm = assertStat.description;
                           //logPreValue(nm,cemap);
                           Boolean v = findPreValue(nm,info.cemap);
                            //log.note("jml.message",nm + " " + v);
                           if (v != null && !v) {
                                int pdetail2 = 0;
                                while (true) {
                                    pdetail2++;
                                    String nmm = nm + "_" + pdetail2;
                                    Boolean vv = findPreValue(nmm,info.cemap);
                                    //log.note("jml.message",nmm + " " + vv);
                                    if (vv == null && pdetail2 > 6) break;
                                    if (true || !vv) {
                                        int pdetail3 = 0;
                                        while (true) {
                                            pdetail3++;
                                            String nmmm = nmm + "_" + pdetail3;
                                            Boolean vvv = findPreValue(nmmm,info.cemap);
                                            //log.note("jml.message",nmmm + " " + vvv);
                                            if (vvv == null) break;
                                            if (!vvv) {
                                                JCTree s = findPreExpr(nmmm,info.cemap);
                                                JavaFileObject prevv = log.useSource(jmlesc.assertionAdder.preconditionDetailClauses.get(nmmm));
                                                log.warning(s.pos,"esc.false.precondition.conjunct", s.toString());
                                                log.useSource(prevv);
                                                break;
                                            } else {
                                                continue;
                                            }
                                        }
                                    } else {
                                        // FIXME - there cannot be a true value here
                                    }
                                }
                            }
                        }
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
            JCExpression p = reportInvalidAssertion(b,info,terminationPos,pathCondition);
            if (p != null) return p;
        }
        return null; // Did not find anything in this block or its followers
    }
    
    protected void logPreValue(String preid, Map<JCTree,String> cemap) {
        BiMap<JCTree,JCTree> bimap = jmlesc.assertionAdder.exprBiMap;
        JCTree s = null;
        for (JCTree t: bimap.forward.keySet()) {
            JCTree n = bimap.getf(t);
            if (n != null && n.toString().contains(preid)) log.note("jml.message",  t.toString() + " >>> " + n);
        }
            for (JCTree t: bimap.reverse.keySet()) { 
//            if (t instanceof JCIdent && ((JCIdent)t).name.toString().contains(preid)) { 
            if (t instanceof JCIdent && t.toString().contains(preid)) {
                s = bimap.getr(t); 
                String vs = s == null ? null : cemap.get(s);
                Boolean v = vs == null ? null : "true".equals(vs);
                log.note("jml.message", t + " <<< " +  s + " " + vs + " " + v );
            }
        }
    }

    protected Boolean findPreValue(String preid, Map<JCTree,String> cemap) {
        BiMap<JCTree,JCTree> bimap = jmlesc.assertionAdder.exprBiMap;
        JCTree s = null;
        for (JCTree t: bimap.reverse.keySet()) { 
            if (t instanceof JCIdent && ((JCIdent)t).name.toString().equals(preid)) { 
                s = bimap.getr(t); 
                break; 
            }
        }
        String vs = s == null ? null : cemap.get(s);
        Boolean v = vs == null ? null : "true".equals(vs);
        return v;
    }

    protected JCTree findPreExpr(String preid, Map<JCTree,String> cemap) {
        BiMap<JCTree,JCTree> bimap = jmlesc.assertionAdder.exprBiMap;
        JCTree s = null;
        for (JCTree t: bimap.reverse.keySet()) { 
            if (t instanceof JCIdent && ((JCIdent)t).name.toString().equals(preid)) { 
                s = bimap.getr(t); 
                break; 
            }
        }
        return s;
    }

    /** Query the solver for the (boolean) value of an id in the current model */
    public Boolean getBoolValue(String id, SMT smt, ISolver solver) {
        String v = getValue(id,smt,solver);
        if (v == null) return null;
        return !v.contains("false");
    }
    
    /** Query the solver for the (boolean) value of an id in the current model */
    public Boolean getBoolValueOrNull(String id, SMT smt, ISolver solver) {
        String v = getValue(id,smt,solver,false);
        if (v == null) return null;
        return !v.contains("false");
    }
    
    /** Query the solver for the (int) value of an id in the current model */
    public int getIntValue(String id, SMT smt, ISolver solver) {
        return Integer.parseInt(getValue(id,smt,solver,true));
    }

    public String getValue(String id, SMT smt, ISolver solver) {
    	return getValue(id,smt,solver,true);
    }
    
    /** Query the solver for any type of value of an id in the current model;
     * if 'report' is true then emit an error message if the response to the query
     * by the solver is an error or is null. 
     */
    public String getValue(String id, SMT smt, ISolver solver, boolean report) {
        org.smtlib.IExpr.ISymbol s = smt.smtConfig.exprFactory.symbol(id);
        IResponse resp = null;
        try {
            resp = solver.get_value(s);
        } catch (StackOverflowError e) {
            // Cannot call log.error here or we risk StackOverflow again
            String emergencyError = "Stack overflow when querying solver for the value of '" + s + "'";
            throw new RuntimeException(emergencyError,e);  // FIXME - a better exception type to use?
        }
        String out;
        if (resp instanceof IResponse.IError) {
            if (report) log.error("jml.internal.notsobad", ((IResponse.IError)resp).errorMsg()); //$NON-NLS-1$
            return null;
        } else if (resp == null) {
            if (report) log.error("jml.internal.notsobad", "Could not find value of assertion: " + id); //$NON-NLS-1$
            return null;
        } else if (resp instanceof org.smtlib.sexpr.ISexpr.ISeq){
            org.smtlib.sexpr.ISexpr se = ((org.smtlib.sexpr.ISexpr.ISeq)resp).sexprs().get(0);
            if (se instanceof org.smtlib.sexpr.ISexpr.ISeq) se = ((org.smtlib.sexpr.ISexpr.ISeq)se).sexprs().get(1);
            out = se.toString();

        } else if (resp instanceof IResponse.IValueResponse) {
            out = ((IResponse.IValueResponse)resp).values().get(0).second().toString(); //FIXME use a printer instead of toString()
        } else {
            log.error("jml.internal.notsobad", "Unexpected response on requesting value of assertion: " + smt.smtConfig.defaultPrinter.toString(resp)); //$NON-NLS-1$
            return null;

        }
        return ((Tracer)tracer).normalizeConstant(out); // FIXME - fix interface
    }
    

    /** If the type of the result is char, then adjust the output to show char values
     * and not just the int value.
     */
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
        void clear();
    }
    
    /** This class walks the expression subtrees, printing the value of each
     * subexpression to the internal StringBuilder. It is used by creating an instance of the Tracer (using
     * the constructor), and then calling scan() on an AST. scan() is called
     * recursively to find and print all subexpressions. Statements are not printed
     * but are scanned for any subexpressions.
     */
    // Not static so we have access to getValue
    public class Tracer extends JmlTreeScanner implements ITracer {
        SMT smt;
        ISolver solver;
        Map<JCTree,String> cemap;
        Log log;
        String result;
        StringBuilder traceText = new StringBuilder();
        
        public void append(String s) {
            traceText.append(s);
        }
        
        public void appendln(String s) {
            traceText.append(s);
            traceText.append(Strings.eol);
        }
        
        public void trace(JCTree that) {
            scan(that);
        }
        
        public String text() {
            return traceText.toString();
        }
        
        public void clear() {
            traceText.setLength(0);
        }
        
        /** Not to be used by callers - this is set false by some visit methods
         * to prevent scan() from printing the value of the expression under
         * scrutiny.
         */
        protected boolean print = true;
        protected boolean subexpressions = true;
        
        public Tracer(Context context, SMT smt, ISolver solver, Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap) {
            this.smt = smt;
            this.solver = solver;
            this.cemap = cemap;
            this.log = Log.instance(context);
        }
        
        public void scan(JCTree that) {
            try {
                if (subexpressions) super.scan(that);
                if (that instanceof JCExpression && !treeutils.isATypeTree((JCExpression)that)) {
                    if (print) {
                        String expr = that.toString();
                        String sv = cemap.get(that);
                        if (sv == null) return;  // Comment this line out to show values that are not in the counterexample
                        if (sv == null && that instanceof JCIdent) {
                            sv = getValue(expr,smt,solver,false); // Fail softly
                        }
                        String userString = normalizeConstant(sv);
                        if (that.type.getTag() == TypeTag.BOOLEAN) { 
                            userString = userString.replaceAll("\\( _ bv0 1 \\)", "false");
                            userString = userString.replaceAll("\\( _ bv1 1 \\)", "true");
                            userString = userString.replaceAll("\\( not true \\)", "false");
                            userString = userString.replaceAll("\\( not false \\)", "true");
                        }
                        if (userString.startsWith("#x")) {
                            try {
                                Long v = Long.valueOf(userString.substring(2),16);
                                userString = userString + " (" + v + ")";
                            } catch (NumberFormatException e) {
                                // Just skip - don't try to add additional information
                            }
                        }

                        if (that.type.getTag() == TypeTag.CHAR) userString = showChar(userString);
                        traceText.append("\t\t\tVALUE: " + expr + "\t === " + userString);
                        traceText.append(Strings.eol);
                    } else {
                        // Turn printing back on, after being turned off because of a void return
                        print = true;
                    }
                }
            } catch (Exception e) {
                traceText.append("\t\t\tVALUE: " + that + "\t === " + "<Internal Exception>");
                traceText.append(Strings.eol);
            }
        }
        
        public String normalizeConstant(String sv) {
            String userString = sv == null ? "???" : constantTraceMap.get(sv);
            if (userString == null) userString = sv;
            return userString;
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
                cemap.put(e, sv);
            }
            if (e.type.getTag() == TypeTag.CHAR) sv = showChar(sv); 
            traceText.append("\t\t\tVALUE: " + e.sym + " = " + 
                        (sv == null ? "???" : sv));
            traceText.append(Strings.eol);

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
            if (tree.getTag() == JCTree.Tag.OR) {
                scan(tree.lhs);
                String v = cemap.get(tree.lhs);
                if (!"true".equals(v)) scan(tree.rhs);
            } else if (tree.getTag() == JCTree.Tag.AND) {
                scan(tree.lhs);
                String v = cemap.get(tree.lhs);
                if (!"false".equals(v)) scan(tree.rhs);
            } else {
                super.visitBinary(tree);
            }
        }

        /** Overridden to handle short-circuit cases appropriately */
        @Override
        public void visitJmlBinary(JmlBinary tree) {
            // Special handling of short-circuit cases
            if (tree.op == JmlTokenKind.IMPLIES) {
                scan(tree.lhs);
                String v = cemap.get(tree.lhs);
                if ("true".equals(v)) scan(tree.rhs);
            } else if (tree.op == JmlTokenKind.REVERSE_IMPLIES) {
                scan(tree.lhs);
                String v = cemap.get(tree.lhs);
                if ("false".equals(v)) scan(tree.rhs);
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
            if (tree.type.getTag() == TypeTag.VOID) print = false;
        }
        
        @Override
        public void visitLambda(JCLambda tree) {
            // Cannot trace anything in a lambda expression
        }

        @Override
        public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
            if (tree.token != JmlTokenKind.BSTYPELC) {
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
    
    static public String benchmarkName = null;
    static private int benchmarkCount = 0;
    
    public void setBenchmark(String solverName, String methodname, SMT.Configuration config) {
        String benchmarkDir = JmlOption.value(context,JmlOption.BENCHMARKS);
        if (benchmarkDir == null || benchmarkDir.isEmpty()) return;
        new java.io.File(benchmarkDir).mkdirs();
        String n;
        if (benchmarkName != null) {
            if ("<init>".equals(methodname)) methodname = "INIT";
            int count = 0;
            String root = benchmarkDir + "/" + benchmarkName + "." + methodname;
            n = root + ".smt2";
            while (true) {
                Path p = FileSystems.getDefault().getPath(n);
                if (!java.nio.file.Files.exists(p)) break;
                count++;
                n = root + (-count) + ".smt2";
            }
        } else {
            benchmarkCount++;
            n = String.format("%s/bench-%05d.smt2",benchmarkDir,benchmarkCount);
        }
//        try {
        config.logfile = n;
//            Path p = FileSystems.getDefault().getPath(n);
//            java.nio.file.Files.deleteIfExists(p);
//            java.nio.file.Files.move(FileSystems.getDefault().getPath("solver.out.z3"),p);
//        } catch (IOException e) {
//            System.out.println(e);
//        }
    }
    
    /** Construct the mapping from original source subexpressions to values in the current solver model. */
    public Map<JCTree,String> constructCounterexample(JmlAssertionAdder assertionAdder, BasicBlocker2 basicBlocker, SMTTranslator smttrans, SMT smt, ISolver solver) {
        boolean verbose = false;
        if (verbose) {
            log.getWriter(WriterKind.NOTICE).println("ORIGINAL <==> TRANSLATED");
            for (JCTree e: assertionAdder.exprBiMap.forward.keySet()) {
                if (!(e instanceof JCExpression) && !(e instanceof JCVariableDecl)) continue;
                JCTree v = assertionAdder.exprBiMap.getf(e);
                if (v != null && assertionAdder.exprBiMap.getr(v) == e) {
                    log.getWriter(WriterKind.NOTICE).println(e.toString() + " <==> " + v);
                } else {
                    log.getWriter(WriterKind.NOTICE).println(e.toString() + " ===> " + v);
                }
            }
            log.getWriter(WriterKind.NOTICE).println("\nTRANSLATED <==> BB");
            for (JCTree e: basicBlocker.bimap.forward.keySet()) {
                JCExpression v = basicBlocker.bimap.getf(e);
                if (v != null && basicBlocker.bimap.getr(v) == e) {
                    log.getWriter(WriterKind.NOTICE).println(e.toString() + " <==> " + v);
                } else {
                    log.getWriter(WriterKind.NOTICE).println(e.toString() + " ===> " + v);
                }
            }
            log.getWriter(WriterKind.NOTICE).println("\nBB <==> SMT");
            for (JCExpression e: smttrans.bimap.forward.keySet()) {
                IExpr v = smttrans.bimap.getf(e);
                if (v != null && smttrans.bimap.getr(v) == e) {
                    log.getWriter(WriterKind.NOTICE).println(e.toString() + " <==> " + v);
                } else {
                    log.getWriter(WriterKind.NOTICE).println(e.toString() + " ===> " + v);
                }
            }
            log.getWriter(WriterKind.NOTICE).println("\nORIGINAL <==> SMT");
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
  //          if (t1 != null && t1.toString().contains("CPRE__4_4")) Utils.stop();
           // t1 is the result of JmlAssertionAdder, which should be a new AST
            JCExpression t2 = basicBlocker.bimap.getf(t1);
            // t2 is the result of BasicBlocker2, which may have changed AST nodes in place
            if (t2 == null && t1 instanceof JCIdent) t2 = (JCIdent)t1; // this can happen if the Ident ends up being declared in a declaration (such as with field or array assignments)

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
            if (verbose) {
                log.getWriter(WriterKind.NOTICE).println(t + " >>>> " + t1 + " >>>> " + t2 + " >>>> " + 
                    smt.smtConfig.defaultPrinter.toString(smtexpr) + " >>>> "+ t3);
            }
        }
        return values;
    }

    /** This is a listener for SMT log and error messages */
    public static class SMTListener implements org.smtlib.Log.IListener {
        org.smtlib.IPrinter printer;
        com.sun.tools.javac.util.Log log;
        
        public SMTListener(Log log, org.smtlib.IPrinter printer) {
            this.log = log;
            this.printer = printer;
        }
        
        @Override
        public void logOut(String msg) {
            log.getWriter(WriterKind.NOTICE).println(msg);
        }

        @Override
        public void logOut(IResponse result) {
            log.getWriter(WriterKind.NOTICE).println(printer.toString(result));
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
            log.getWriter(WriterKind.NOTICE).println(msg);
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
    
    /** Allows other extending classes to implement a different type of proof **/
    public SMTTranslator getTranslator(Context context, String def){
        return new SMTTranslator(context, def);
    }
}


