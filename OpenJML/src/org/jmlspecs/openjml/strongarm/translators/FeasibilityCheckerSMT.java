package org.jmlspecs.openjml.strongarm.translators;

import java.io.PrintWriter;
import java.util.Date;
import java.util.List;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.esc.BasicBlocker2;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.JmlEsc;
import org.jmlspecs.openjml.esc.MethodProverSMT;
import org.jmlspecs.openjml.esc.SMTTranslator;
import org.jmlspecs.openjml.esc.MethodProverSMT.SMTListener;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.strongarm.JmlInferPostConditions;
import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.SMT;
import org.smtlib.IVisitor.VisitorException;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log.WriterKind;

public class FeasibilityCheckerSMT extends MethodProverSMT {
    
    

    /** don't use this constructor **/
    public FeasibilityCheckerSMT(JmlEsc jmlesc) {
        super(jmlesc);
        
    }
    
    /** use this one **/
    public FeasibilityCheckerSMT(Context context){
        this(new JmlEsc(context));
        
        jmlesc.assertionAdder = JmlInferPostConditions.instance(context).assertionAdder;

    }
    
    
    /** Allows other extending classes to implement a different type of proof **/
    @Override
    public SMTTranslator getTranslator(Context context, String def){
        return new SMTTranslator(context, def);
    }
    
    public boolean checkFeasible(Set<JmlMethodClauseExpr> filters /* should be the set of all REQUIRES */ , JmlMethodDecl method){
        
        // get the default prover 
        String proverToUse = jmlesc.pickProver();
        
        IProverResult result = prove(method, proverToUse, filters);
        
        if(result!=null && result.result()==IProverResult.UNSAT){
            return false;
        }
        
        return true; // if we don't know (SAT or UNKNOWN) we say it's maybe possible still
        
    }
    
    public JCExpression convertToConjunction(Set<JmlMethodClauseExpr> filters){
        
        if(filters == null || filters.size()==0){
            return null;
        }
        
        JCExpression P = null;
        // construct the P 
        for(JmlMethodClauseExpr expr : filters){
            if(P==null){
                P = expr.expression;
            }else{
                P = treeutils.makeBinary(0, JCTree.Tag.AND, expr.expression, P);
            }
        }
        
        return P;
    }
    
    public IProverResult prove(JmlMethodDecl methodDecl, String proverToUse, Set<JmlMethodClauseExpr> filters) {
        escdebug = escdebug || utils.jmlverbose >= Utils.JMLDEBUG;
        boolean verbose = escdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
                || utils.jmlverbose >= Utils.JMLVERBOSE;
        boolean showSubexpressions = verbose || JmlOption.isOption(context,JmlOption.SUBEXPRESSIONS);
        boolean showTrace = this.showSubexpressions || JmlOption.isOption(context,JmlOption.TRACE);
        boolean showCounterexample = showTrace || JmlOption.isOption(context,JmlOption.COUNTEREXAMPLE);
        boolean showBBTrace = escdebug;
        
        log.useSource(methodDecl.sourcefile);

        boolean printPrograms = JmlOption.isOption(context, JmlOption.SHOW);
        boolean print = printPrograms;
        
        JmlClassDecl currentClassDecl = utils.getOwner(methodDecl);
        
        // FIXME - when might methodDecl.sym be null?
        JmlMethodSpecs denestedSpecs = methodDecl.sym == null ? null : 
            JmlSpecs.instance(context).getDenestedSpecs(methodDecl.sym);

        // newblock is the translated version of the method body
        JmlMethodDecl translatedMethod = jmlesc.assertionAdder.methodBiMap.getf(methodDecl).getTranslation("");
        if (translatedMethod == null) {
            log.warning("jml.internal","No translated method for " + utils.qualifiedMethodSig(methodDecl.sym));
            return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.SKIPPED,null);
        }
        JCBlock newblock = translatedMethod.getBody();
        if (newblock == null) {
            log.error("esc.no.typechecking",methodDecl.name.toString()); //$NON-NLS-1$
            return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,null);
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
        SMTTranslator smttrans = getTranslator(context, methodDecl.sym.toString()); 
        
        ISolver solver =null;
        
        try {
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
                if (printPrograms) {
                    log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                    log.getWriter(WriterKind.NOTICE).println(separator);
                    log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                    log.getWriter(WriterKind.NOTICE).println("BasicBlock2 FORM of " + utils.qualifiedMethodSig(methodDecl.sym));
                    log.getWriter(WriterKind.NOTICE).println(program.toString());
                }
    
                // convert the basic block form to SMT
                try {
                    script = new SMTTranslator(context, methodDecl.sym.toString()).convert(program,smt,true); 
                    if (printPrograms) {
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
                } catch (Exception e) {
                    log.error("jml.internal", "Failed to convert to SMT: " + e);
                    return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,new Date());
                }
                // Starts the solver (and it waits for input)
                start = new Date();
                setBenchmark(proverToUse,methodDecl.name.toString(),smt.smtConfig);
                solver = smt.startSolver(smt.smtConfig,proverToUse,exec);
                if (solver == null) { 
                    log.error("jml.solver.failed.to.start",exec);
                    return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start);
                } else {
                    // Try the prover
                    if (verbose) log.getWriter(WriterKind.NOTICE).println("EXECUTION"); //$NON-NLS-1$
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
                log.getWriter(WriterKind.NOTICE).println("Proof result is " + smt.smtConfig.defaultPrinter.toString(solverResponse));
            }
    
            IProverResult proofResult = null;
    
            IResponse unsatResponse = smt.smtConfig.responseFactory.unsat();
            
            if (solverResponse.isError()) {
                solver.exit();
                log.error("jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start);
            }
            
            
            // two steps. first we check that the result was 
            if (!solverResponse.equals(unsatResponse)) {
                return null;
            }
            
            if (verbose) log.getWriter(WriterKind.NOTICE).println("Method checked OK");
    
            
            proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNSAT,start);
            
            try {
    
                solver.pop(1); // Pop off previous check_sat
    
                List<JmlStatementExpr> checks = jmlesc.assertionAdder.assumeChecks.get(methodDecl.sym.toString()); // FIXME - needs sp[litkey
                
                // we want to convert the filters and the current proposition into a statement like this: 
                //
                // !(filters => prop)
                //
                // this is always true (and thus can be pruned iff it's unsat)
                
                
                if(checks==null) return null;
                
                solver.pop(1);  // Pop off previous setting of assumeCheck
                solver.push(1); // Mark the top
    
                JCExpression converted = convertToConjunction(filters);
                
    
                // don't know
                if(converted==null){
                    return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.POSSIBLY_SAT,start);
                }
                
                solver.assertExpr(smttrans.convertExpr(converted)); 
    
                solverResponse = solver.check_sat();
            
                utils.progress(1,1, "Seeing if specification case is SAT: " + converted.toString());
                
                
                utils.progress(1,1, "SAT Check - " + converted.toString() + " : " +
                        (solverResponse.equals(unsatResponse) ? "NOT FEASIBLE": "FEASIBLE"));
                
                
                if (solverResponse.equals(unsatResponse)) {
                    proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNSAT,start);
                } else if (solverResponse.isError()) {
                    log.error("jml.esc.badscript", methodDecl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                    proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start);
                } else{
                    proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.POSSIBLY_SAT,start);
                }
                
            } finally {            
                solver.exit();
                smt.smtConfig.logfile = null;
            }
    
            return proofResult;
        }finally{
            try {
                solver.exit();
            }catch(Exception e){}
        }
    }
}