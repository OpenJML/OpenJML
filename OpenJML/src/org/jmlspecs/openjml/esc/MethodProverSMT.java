package org.jmlspecs.openjml.esc;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.Span;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IResponse;
import org.smtlib.IResponse.IPair;
import org.smtlib.ISolver;
import org.smtlib.SMT;
import org.smtlib.IResponse.IError;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.sexpr.ISexpr;
import org.smtlib.solvers.Solver_yices;
import org.smtlib.solvers.Solver_yices2;

import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Position;

public class MethodProverSMT {

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
    
    // FIXME DOCUMENT
    protected Tracer tracer;
    


    /** true if compiler options are set to a verbose mode */
    boolean verbose;
    
    /** Just for debugging esc */
    public static boolean escdebug = false; // May be set externally to enable debugging while testing
    

    public MethodProverSMT(JmlEsc jmlesc) {
        this.jmlesc = jmlesc;
        this.context = jmlesc.context;
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
    }
    
    public IProverResult prove(JmlMethodDecl methodDecl) {
        escdebug = escdebug || utils.jmlverbose >= Utils.JMLDEBUG;
        this.verbose = escdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
                || utils.jmlverbose >= Utils.JMLVERBOSE;
        this.showSubexpressions = this.verbose || JmlOption.isOption(context,JmlOption.SUBEXPRESSIONS);
        this.showTrace = verbose || this.showSubexpressions || JmlOption.isOption(context,JmlOption.TRACE);
        this.showCounterexample = this.showTrace || JmlOption.isOption(context,JmlOption.COUNTEREXAMPLE);
        this.showBBTrace = verbose;

        boolean print = jmlesc.verbose;
        boolean printPrograms = print || JmlOption.isOption(context, JmlOption.SHOW);
        

        JmlClassDecl currentClassDecl = utils.getOwner(methodDecl);
        
        JmlMethodSpecs denestedSpecs = methodDecl.sym == null ? null : jmlesc.specs.getDenestedSpecs(methodDecl.sym);

        JCBlock newblock = jmlesc.assertionAdder.methodBiMap.getf(methodDecl).getBody();
        if (printPrograms) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("TRANSFORMATION OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            log.noticeWriter.println(JmlPretty.write(newblock));
        }

        // determine the executable
        String exec = jmlesc.pickProverExec(jmlesc.proverToUse);
        if (exec == null) {
            log.warning("esc.no.exec",jmlesc.proverToUse); //$NON-NLS-1$
            return new ProverResult(jmlesc.proverToUse,IProverResult.SKIPPED);
        }
        
        // create an SMT object, adding any options
        SMT smt = new SMT();
        smt.processCommandLine(new String[]{}, smt.smtConfig);

        // Add a listener for errors and start the solver.
        // The listener is set to use the defaultPrinter for printing 
        // SMT abstractions and forwards all informational and error messages
        // to the OpenJML log mechanism
        smt.smtConfig.log.addListener(new SMTListener(log,smt.smtConfig.defaultPrinter));
        SMTTranslator smttrans = new SMTTranslator(context);

        ISolver solver;
        IResponse solverResponse ;
        BasicBlocker2 basicBlocker;
        BasicProgram program;
        {
            // now convert to basic block form
            basicBlocker = new BasicBlocker2(context);
            program = basicBlocker.convertMethodBody(newblock, methodDecl, denestedSpecs, currentClassDecl, jmlesc.assertionAdder);
            if (printPrograms) {
                log.noticeWriter.println(Strings.empty);
                log.noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
                log.noticeWriter.println(Strings.empty);
                log.noticeWriter.println("BasicBlock2 FORM of " + utils.qualifiedMethodSig(methodDecl.sym) + JmlTree.eol +
                        program.toString());
            }

            // convert the basic block form to SMT
            ICommand.IScript script = smttrans.convert(program,smt);
            if (printPrograms) {
                try {
                    log.noticeWriter.println(Strings.empty);
                    log.noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
                    log.noticeWriter.println(Strings.empty);
                    log.noticeWriter.println("SMT TRANSLATION OF " + utils.qualifiedMethodSig(methodDecl.sym));
                    org.smtlib.sexpr.Printer.write(new PrintWriter(log.noticeWriter),script);
                    log.noticeWriter.println();
                    log.noticeWriter.println();
                } catch (VisitorException e) {
                    log.noticeWriter.print("Exception while printing SMT script: " + e); //$NON-NLS-1$
                }
            }

            solver = smt.startSolver(smt.smtConfig,jmlesc.proverToUse,exec);

            // Try the prover
            if (jmlesc.verbose) log.noticeWriter.println("EXECUTION"); //$NON-NLS-1$
            solverResponse = script.execute(solver); // Note - the solver knows the smt configuration

        }
        
        
    
        IProverResult proofResult = null;

        {
            if (solverResponse.isError()) {
                solver.exit();
                log.error("jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                return new ProverResult(jmlesc.proverToUse,IProverResult.ERROR);
            }
            if (print) log.noticeWriter.println(smt.smtConfig.defaultPrinter.toString(solverResponse));
            if (solverResponse.toString().equals("unsat")) {// FIXME - should have a better means of checking this
                if (jmlesc.verbose) log.noticeWriter.println("Method checked OK");
                proofResult = new ProverResult(jmlesc.proverToUse,IProverResult.UNSAT);
                
                if (!JmlOption.value(context,JmlOption.FEASIBILITY).equals("none")) {
                    java.util.List<JCTree.JCParens> a = jmlesc.assertionAdder.assumptionChecks.get(methodDecl.sym);
                    boolean first = true;
                    if (a != null) for (JCParens assumptionExpr: a) { // FIXME - warn if a null? perhaps just an artifact of assertig a constructor
                        JCExpression prevExpr = assumptionExpr.expr;
                        assumptionExpr.expr = JmlTreeUtils.instance(context).falseLit;
                        try {
                            BasicBlocker2 basicBlocker2 = new BasicBlocker2(context);
                            BasicProgram program2 = basicBlocker2.convertMethodBody(newblock, methodDecl, denestedSpecs, currentClassDecl, jmlesc.assertionAdder);
                            if (printPrograms) {
                                log.noticeWriter.println(Strings.empty);
                                log.noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
                                log.noticeWriter.println(Strings.empty);
                                log.noticeWriter.println("BASIC BLOCK FORM OF " 
                                        + utils.qualifiedMethodSig(methodDecl.sym)
                                        + " FOR CHECKING FEASIBILITY"
                                        + JmlTree.eol
                                        + program2.toString());
                            }

                            // create an SMT object, adding any options
                            smt.processCommandLine(new String[]{}, smt.smtConfig);

                            // convert the basic block form to SMT
                            SMTTranslator smttrans2 = new SMTTranslator(context);
                            ICommand.IScript script2 = smttrans2.convert(program2,smt);


                            ISolver solver2 = smt.startSolver(smt.smtConfig,jmlesc.proverToUse,exec);

                            // Try the prover
                            if (jmlesc.verbose) log.noticeWriter.println("EXECUTION"); //$NON-NLS-1$
                            solverResponse = script2.execute(solver2); // Note - the solver knows the smt configuration
                            solver2.exit();
                            if (solverResponse.toString().equals("unsat")) {
                                if (first) {
                                	log.warning(assumptionExpr.pos(), "esc.infeasible.preconditions", utils.qualifiedMethodSig(methodDecl.sym));
                                    proofResult = new ProverResult(jmlesc.proverToUse,IProverResult.INCONSISTENT);
                                    // If the preconditions are inconsistent, all subsequent paths will be infeasible as well
                                    break;
                                } else {
                                	log.warning(assumptionExpr.pos(), "esc.infeasible.assumption", utils.qualifiedMethodSig(methodDecl.sym));
                                    proofResult = new ProverResult(jmlesc.proverToUse,IProverResult.INCONSISTENT);
                                }
                            }
                        } finally {
                        	first = false;
                            assumptionExpr.expr = prevExpr;
                        }
                        if (!JmlOption.value(context, JmlOption.FEASIBILITY).equals("all")) break;
                    }
                }
            } else {
                int count = Utils.instance(context).maxWarnings;
                while (true) {
                    if (print) log.noticeWriter.println("Some assertion not valid");

                    if (showCounterexample) {
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
                    tracer = new Tracer(context,smt,solver,cemap,jmap);
                    jmlesc.mostRecentCEMap = cemap;
                    // Report JML-labeled values and the path to the failed invariant
                    if (showTrace) log.noticeWriter.println("\nTRACE\n");
                    path = new ArrayList<IProverResult.Span>();
                    JCExpression pathCondition = reportInvalidAssertion(program,smt,solver,methodDecl,cemap,jmap);
                    
                    if (proofResult == null) {
                        ProverResult pr = new ProverResult(jmlesc.proverToUse,
                            solverResponse.toString().equals("sat") ? IProverResult.SAT : IProverResult.POSSIBLY_SAT);
                        if (pathCondition != null) {
                            Counterexample ce = new Counterexample(cemap,path);
                            pr.add(ce);
                        }
                        proofResult = pr;
                    }
                    
                    if (pathCondition == null) {
                        break;
                    }


                    //                if (showCounterexample) {
                    //                    log.noticeWriter.println("\nTRACE with respect to ORIGINAL PROGRAM\n");
                    //                }

                    if (--count <= 0) break;
                    //if (solver instanceof Solver_yices2 || solver instanceof Solver_yices) break;
                    
                    solver.pop(1);
                    solver.assertExpr(smttrans.convertExpr(pathCondition));
                    solver.push(1);
                    solverResponse = solver.check_sat();

                    if (solverResponse.isError()) {
                        log.error("jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                        return new ProverResult(jmlesc.proverToUse,IProverResult.ERROR);
                    }
                    if (solverResponse.toString().equals("unsat")) break;
                    // TODO -  checking each assertion separately
                }
            }
        }
        solver.exit();
        jmlesc.mostRecentProgram = program;
        return proofResult;
        
    }
    
    protected List<IProverResult.Span> path;


    /** Iterates through the basic blocks to find and report the invalid assertion
     * that caused the SAT result from the prover.
     */
    public JCExpression reportInvalidAssertion(BasicProgram program, SMT smt, ISolver solver, JCMethodDecl decl,
            Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap) {
        showTrace = true;
        exprValues = new HashMap<JCTree,String>();
        JCExpression pathCondition = reportInvalidAssertion(program.startBlock(),smt,solver,decl,0, JmlTreeUtils.instance(context).falseLit,cemap,jmap);
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
            Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap) {
        String id = block.id.name.toString();
        boolean value = getBoolValue(id,smt,solver);
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
        boolean printspans = true;        
        for (JCStatement stat: block.statements()) {
            // Report any statements that are JML-labeled
            if (stat instanceof JCVariableDecl) {
                Name n = ((JCVariableDecl)stat).name;
                String ns = n.toString();
                if (ns.startsWith(Strings.labelVarString)) {
                    boolean b = getBoolValue(ns,smt,solver);
                    if (ns.startsWith(prefix_lblpos)) {
                        if (b) log.warning(stat.pos,"esc.label.value",ns.substring(prefix_lblpos.length()),b); //$NON-NLS-1$
                    } else if (ns.startsWith(prefix_lblneg)) {
                        if (!b) log.warning(stat.pos,"esc.label.value",ns.substring(prefix_lblneg.length()),b); //$NON-NLS-1$
                    } else if (ns.startsWith(prefix_lbl)) {
                        log.warning(stat.pos,"esc.label.value",ns.substring(prefix_lbl.length()),b); //$NON-NLS-1$
                    } else {
                        log.warning(stat.pos,"jml.internal.notsobad","Unknown label: " + ns); //$NON-NLS-1$
                    }
                }
            }
            
            if (showTrace) {
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
            if (stat instanceof JmlVariableDecl) {
                if (!((JmlVariableDecl)stat).name.toString().startsWith(Strings.tmpVarString)) {
                    int sp = stat.getStartPosition();
                    int ep = stat.getEndPosition(log.currentSource().getEndPosTable());
                    if (printspans) log.noticeWriter.println("SPAN " + sp + "  " + ep + " " + stat);
                    if (ep <= sp) {
                        if (printspans) log.noticeWriter.println("BAD SPAN " + sp + "  " + ep + " " + stat);
                    }
                    else path.add(new Span(sp,ep,Span.NORMAL));
                }
            } else if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlToken.ASSUME) {
                JmlStatementExpr assumeStat = (JmlStatementExpr)stat;
                JCExpression e = assumeStat.expression;
                int sp = e.getStartPosition();
                int ep = e.getEndPosition(log.currentSource().getEndPosTable());
                Label label = assumeStat.label;
                if (label == Label.ASSIGNMENT) {
                    if (printspans) log.noticeWriter.println("SPAN " + label + " " + sp + "  " + ep + " " + e);
                    if (ep <= sp) {
                        if (printspans) log.noticeWriter.println("BAD SPAN " + label + " " + sp + "  " + ep + " " + e);
                    }
                    else path.add(new Span(sp,ep,Span.NORMAL));
                } else if (label == Label.EXPLICIT_ASSUME) {
                    if (printspans) log.noticeWriter.println("SPAN " + label + " " + sp + "  " + ep + " " + stat);
                    if (ep <= sp) {
                        if (printspans) log.noticeWriter.println("BAD SPAN " + label + " " + sp + "  " + ep + " " + e);
                    }
                    else {
//                        if (e instanceof JCTree.JCLiteral) {
//                            value = ((JCTree.JCLiteral)e).value.equals(1); // Boolean literals have 0 and 1 value
//                        } else if (e instanceof JCTree.JCParens) {
//                                value = ((JCTree.JCLiteral)((JCTree.JCParens)e).expr).value.equals(1); // Boolean literals have 0 and 1 value
//                        } else {
//                            id = ((JCIdent)e).name.toString(); // FIXME _ assumes are not necessarily IDENTS?
//                            value = getBoolValue(id,smt,solver);
//                        }
                        path.add(new Span(sp,ep,Span.NORMAL)); //value ? Span.TRUE : Span.FALSE));
                    }
                } else if (label == Label.BRANCHT || label == Label.BRANCHE || label == Label.SWITCH_VALUE || label == Label.CASECONDITION) {
                    if (printspans) log.noticeWriter.println("SPAN " + label + " " + sp + "  " + ep + " " + e);
                    if (ep <= sp) {
                        if (printspans) log.noticeWriter.println("BAD SPAN " + label + " " + sp + "  " + ep + " " + e);
                    }
                    else path.add(new Span(sp,ep,
                            label == Label.BRANCHT ? Span.TRUE : 
                            label == Label.BRANCHE? Span.FALSE : Span.NORMAL));
                } else if (label == Label.DSA || label == Label.NULL_CHECK || label == Label.NULL_FIELD || label == Label.IMPLICIT_ASSUME) {
                    // Ignore
                } else {
                    // FIXME - at least PRECONDITION
                    if (printspans) log.noticeWriter.println("UNHANDLED LABEL " + label);
                }
            } else if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlToken.ASSERT) {
                JmlStatementExpr assertStat = (JmlStatementExpr)stat;
                JCExpression e = assertStat.expression;
                Label label = assertStat.label;
                if (e instanceof JCTree.JCLiteral) {
                    value = ((JCTree.JCLiteral)e).value.equals(1); // Boolean literals have 0 and 1 value
                } else if (e instanceof JCTree.JCParens) {
                        value = ((JCTree.JCLiteral)((JCTree.JCParens)e).expr).value.equals(1); // Boolean literals have 0 and 1 value
                } else {
                    id = ((JCIdent)e).name.toString(); // Relies on all assert statements being reduced to identifiers
                    value = getBoolValue(id,smt,solver);
                }
                int sp = e.getStartPosition();
                int ep = e.getEndPosition(log.currentSource().getEndPosTable());
                if (printspans) log.noticeWriter.println("SPAN " + label + " " + sp + "  " + ep + " " + e);
                if (ep <= sp) {
                    if (printspans) log.noticeWriter.println("BAD SPAN " + sp + "  " + ep + " " + e);
                }
                else path.add(new Span(sp,ep,
                        value ? Span.TRUE : Span.FALSE));
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
                    int epos = assertStat.getEndPosition(log.currentSource().getEndPosTable());
                    // FIXME: 
                    if (printspans) if (epos == Position.NOPOS) log.noticeWriter.println("INCOMPLETE WARNING RANGE " + assertStat.getStartPosition() + " " + ep + " " + assertStat);
                    if (epos == Position.NOPOS || pos != assertStat.pos) {
                        log.warning(pos,"esc.assertion.invalid",label,decl.getName(),extra); //$NON-NLS-1$
                    } else {
                        // FIXME - migrate to using pos() for terminationPos as well 
                        log.warning(assertStat.pos(),"esc.assertion.invalid",label,decl.getName(),extra); //$NON-NLS-1$
                    }
                    JCDiagnostic diag = JCDiagnostic.Factory.instance(context).note(log.currentSource(), new JCDiagnostic.SimpleDiagnosticPosition(pos), "esc.empty",Strings.empty); //$NON-NLS-1$
                    String msg = diag.toString();
                    msg = msg.substring(0,msg.indexOf("Note")); //$NON-NLS-1$
                    // TODO - above we include the optionalExpression as part of the error message
                    // however, it is an expression, and not evaluated for ESC. Even if it is
                    // a literal string, it is printed with quotes around it.
                    if (prev != null) log.useSource(prev);
                    if (assertStat.associatedPos != Position.NOPOS) {
                        if (assertStat.associatedSource != null) prev = log.useSource(assertStat.associatedSource);
                        log.warning(assertStat.associatedPos, "jml.associated.decl",msg); // FIXME - could add this information, but it would blow Aaway the test results
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
            JCExpression p = reportInvalidAssertion(b,smt,solver,decl,terminationPos,pathCondition,cemap,jmap);
            if (p != null) return p;
        }
        return null; // DId not find anything in this block or its followers
    }

    /** Query the solver for the (boolean) value of an id in the current model */
    public boolean getBoolValue(String id, SMT smt, ISolver solver) {
        String v = getValue(id,smt,solver);
        return v != null && !v.contains("false");
    }
    
    /** Query the solver for the (int) value of an id in the current model */
    public int getIntValue(String id, SMT smt, ISolver solver) {
        return Integer.parseInt(getValue(id,smt,solver));
    }

    /** Query the solver for the (String) value of an id in the current model */
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
        e.accept(tracer);
    }

    
//    /** Write out (through log.noticeWriter) the values of the given expression
//     * and, recursively, of any subexpressions.
//     */
//    public void traceSubExpr(JCExpression e, SMT smt, ISolver solver, Map<JCExpression,String> cemap, BiMap<JCExpression,JCExpression> jmap) {
//        e.accept(tracer);if (e instanceof JCIdent) {
//            Name n = ((JCIdent)e).name;
//            String value = getValue(n.toString(),smt,solver);
//            log.noticeWriter.println("VALUE: " + n + " = " + value);
//            String sv = cemap.get(e);
//            log.noticeWriter.println("V " + n + " : " + jmap.getr(e) + " = " + sv + " :: " + value);
//            return;
//        } else if (e instanceof JCBinary) {
//        } else if (e instanceof JCUnary) {
//            traceSubExpr(((JCUnary)e).arg,smt,solver,cemap,jmap);
//            String sv = cemap.get(e);
//            log.noticeWriter.println("V " + e + " : " + jmap.getr(e) + " = " + sv);
//        } else if (e instanceof JCConditional) {
//            traceSubExpr(((JCConditional)e).arg,smt,solver,cemap,jmap);
//            String sv = cemap.get(e);
//            log.noticeWriter.println("V " + e + " : " + jmap.getr(e) + " = " + sv);
//        }
//        // FIXME - this should be expanded to more kinds of expressions, but only those that might be in a basic program - actually should do this in relation to the original program
//    }
    
    // FIXME - document
    // Not static so we have access to getValue
    public class Tracer extends JmlTreeScanner {
        SMT smt;
        ISolver solver;
        Map<JCTree,String> cemap;
        Log log;
        String result;
        
        public Tracer(Context context, SMT smt, ISolver solver, Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap) {
            this.smt = smt;
            this.solver = solver;
            this.cemap = cemap;
            this.log = Log.instance(context);
        }
        
        @Override
        public void visitIdent(JCIdent e) {
            Name n = e.name;
            String sv = cemap.get(e);
            if (sv != null) log.noticeWriter.println("VALUE: " + n + " = " + sv);
            if (sv == null) {
                sv = getValue(n.toString(),smt,solver);
                log.noticeWriter.println("VALUE Retrieved: " + n + " = " + sv);
                cemap.put(e, sv);
            }
//            JCTree ex = jmap.getr(e);
//            if (ex != null) {
//                log.noticeWriter.println(ex + " === " + sv);
//            } else {
//                //log.noticeWriter.println("VALUE unknown: " + n );
//            }
            result = sv;
        }
        
        @Override
        public void visitJmlVariableDecl(JmlVariableDecl e) {
            Name n = e.name;
            String sv = cemap.get(e);
            log.noticeWriter.println("VALUE: " + n + " = " + sv);
            if (sv == null) {
                sv = getValue(n.toString(),smt,solver);
                log.noticeWriter.println("VALUE Retrieved: " + n + " = " + sv);
                cemap.put(e, sv);
            }

            scan(e.init);
//            JCTree ex = jmap.getr(e);
//            if (sv != null && ex != null) {
//                log.noticeWriter.println(ex + " === " + sv);
//            }
            result = sv;
        }
        
        @Override
        public void visitAssign(JCAssign e) {
            scan(e.lhs);
            scan(e.rhs);
            String sv = cemap.get(e);
//            JCTree ex = jmap.getr(e);
//            if (sv != null && ex != null) {
//                log.noticeWriter.println(ex + " === " + sv);
//            }
            result = sv;
        }
        
        @Override
        public void visitBinary(JCBinary e) {
            e.lhs.accept(this);
            e.rhs.accept(this);
            String sv = cemap.get(e);
//            JCTree ex = jmap.getr(e);
//            if (sv != null && ex != null) {
//                log.noticeWriter.println(ex + " === " + sv);
//            }
            result = sv;
        }
        
        @Override
        public void visitUnary(JCUnary e) {
            e.arg.accept(this);
            String sv = cemap.get(e);
//            JCTree ex = jmap.getr(e);
//            if (sv != null && ex != null) {
//                log.noticeWriter.println(ex + " === " + sv);
//            }
            result = sv;
        }
        
        @Override
        public void visitConditional(JCConditional e) {
            e.cond.accept(this);
            if (result.equals("true")) {
                e.truepart.accept(this);
            } else {
                e.falsepart.accept(this);
            }
            String sv = cemap.get(e);
            result = sv;
        }
        
        @Override
        public void visitSelect(JCFieldAccess tree) {
            if (!JmlTreeUtils.instance(context).isATypeTree(tree)) {
                scan(tree.selected);
                // FIXME - needs more
            }
        }
        
        @Override
        public void visitIndexed(JCArrayAccess tree) {
            scan(tree.indexed);
            scan(tree.index);
                // FIXME - needs more
        }

        @Override
        public void visitTypeCast(JCTypeCast tree) {
            // Overridden to skip scanning the type name: scan(tree.clazz);
            scan(tree.expr);
        }

        @Override
        public void visitTypeTest(JCInstanceOf tree) {
            scan(tree.expr);
            // Overridden to skip scanning the type name: scan(tree.clazz);
        }

        @Override
        public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
            if (tree.token == JmlToken.BSTYPELC) {
                // FIXME - scan for this value?
            } else {
                super.visitJmlMethodInvocation(tree);
            }
        }

        
    }
    
    /** Fetch values for all expressions that are targets of the mapping in smttrans. */
    public Map<String,String> constructSMTCounterexample(SMTTranslator smttrans, ISolver solver) {
        Map<String,String> ce = new HashMap<String,String>();
        IExpr[] ee = new IExpr[1];
        for (IExpr e: smttrans.bimap.forward.values()) {
            String key = smttrans.bimap.getr(e).toString();
            if (ce.get(key) != null) continue;
            ee[0] = e;
            IResponse resp = solver.get_value(ee);
            // FIXME - need to get a singloe kind of response
            if (resp instanceof ISexpr.ISeq) {
                ISexpr pair = ((ISexpr.ISeq)resp).sexprs().get(0);
                ISexpr value = ((ISexpr.ISeq)pair).sexprs().get(1);
                ce.put(key, value.toString());
            }
            if (resp instanceof IResponse.IValueResponse) {
                IPair<IExpr,IExpr> pair = ((IResponse.IValueResponse)resp).values().get(0);
                IExpr value = pair.second();
                ce.put(key, value.toString());
            }
        }
        return ce;
    }
    
    /** Construct the mapping from original source subexpressions to values in the current solver model. */
    public Map<JCTree,String> constructCounterexample(JmlAssertionAdder assertionAdder, BasicBlocker2 basicBlocker, SMTTranslator smttrans, SMT smt, ISolver solver) {
        boolean verbose = false;
        if (verbose) {
            log.noticeWriter.println("ORIGINAL <==> TRANSLATED");
            for (JCTree e: assertionAdder.exprBiMap.forward.keySet()) {
                if (!(e instanceof JCExpression)) continue;
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
        Map<String,String> ce = constructSMTCounterexample(smttrans,solver);
        Map<JCTree,String> values = new HashMap<JCTree,String>();
        for (JCTree t : assertionAdder.exprBiMap.forward.keySet() ) {
            if (!(t instanceof JCExpression)) continue;
            // t is the original source expression
            JCTree t1 = assertionAdder.exprBiMap.getf(t);
            // t1 is the result of JmlAssertionAdder
            JCExpression t2 = basicBlocker.bimap.getf(t1);
            // t2 is the result of BasicBlocker2, which may have changed AST nodes in place
            if (t2 == null && t1 instanceof JCIdent) t2 = (JCIdent)t1; // this can happen if the Ident ends up being declared in a declaration (such as wtih field or array assignments)
            String t3 = t2 == null ? null : ce.get(t2.toString());
            values.put(t, t3);
            if (verbose) log.noticeWriter.println(t + " >>>> " + t1 + " >>>> " + t2 + " >>>> " + t3);
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
            log.error("jml.internal",msg); //$NON-NLS-1$
        }

        @Override
        public void logError(IError result) {
            log.error("jml.internal",printer.toString(result)); //$NON-NLS-1$
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
     * stored as Strings.
     * @author David Cok
     *
     */
    public class Counterexample implements IProverResult.ICounterexample {
        protected SortedMap<String,String> map = new TreeMap<String,String>();
        protected Map<JCTree,String> mapv = new HashMap<JCTree,String>();
        private List<IProverResult.Span> path;
        
        public Counterexample(Map<JCTree,String> cemap, List<IProverResult.Span> path) {
            mapv = cemap;
            this.path = path;
        }
        
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


