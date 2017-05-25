package org.jmlspecs.openjml.strongarm.translators;

import java.io.PrintWriter;
import java.util.Date;
import java.util.List;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.BasicBlocker2;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.esc.JmlEsc;
import org.jmlspecs.openjml.esc.MethodProverSMT;
import org.jmlspecs.openjml.esc.SMTTranslator;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.strongarm.tree.analysis.SpecToExpression;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.SMT;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log.WriterKind;

public class CheckImpliesSMT extends MethodProverSMT {

    /** don't use this constructor **/
    public CheckImpliesSMT(JmlEsc jmlesc) {
        super(jmlesc);

    }

    /** use this one **/
    public CheckImpliesSMT(Context context) {
        this(new JmlEsc(context));
        jmlesc.assertionAdder = new JmlAssertionAdder(context, true, false,
                false);
    }

    /**
     * Allows other extending classes to implement a different type of proof
     **/
    @Override
    public SMTTranslator getTranslator(Context context, String def) {
        return new SMTTranslator(context, def);
    }

    public boolean checkImplies(JmlMethodDecl p, JmlMethodDecl q) {

        /** get the default prover **/
        String proverToUse = jmlesc.pickProver();

        IProverResult result = prove(p, proverToUse, p, q);

        /** if !(p => q) is UNSAT, then p => q is a tautology. **/
        if (result != null && result.result() == IProverResult.UNSAT) {
            return true;
        }

        return false;
    }

    /**
     * we want to create an implication for use in a smt check. we want p => q
     * <==> !p or q. So that we can check to see if this is generally true, we
     * negate again giving us: p and !q
     **/
    public JCExpression convertToImplication(JmlMethodDecl p, JmlMethodDecl q) {

        JCExpression P = SpecToExpression.convertTree(p.cases, treeutils);
        JCExpression Q = SpecToExpression.convertTree(q.cases, treeutils);

        // construct the !Q
        JCExpression Qnot = treeutils.makeNot(0, Q);

        // construct the implication p ^ !q
        return treeutils.makeBinary(0, JCTree.Tag.AND, P, Qnot);
    }

    public IProverResult prove(JmlMethodDecl methodDecl, String proverToUse,
            JmlMethodDecl p, JmlMethodDecl q) {
        escdebug = escdebug || utils.jmlverbose >= Utils.JMLDEBUG;
        boolean verbose = escdebug || JmlOption.isOption(context, "-verbose") // The
                                                                              // Java
                                                                              // verbose
                                                                              // option
                || utils.jmlverbose >= Utils.JMLVERBOSE;
        boolean showSubexpressions = verbose
                || JmlOption.isOption(context, JmlOption.SUBEXPRESSIONS);
        boolean showTrace = showSubexpressions
                || JmlOption.isOption(context, JmlOption.TRACE);
        boolean showCounterexample = showTrace
                || JmlOption.isOption(context, JmlOption.COUNTEREXAMPLE);
        boolean showBBTrace = escdebug;

        boolean printPrograms = JmlOption.isOption(context, JmlOption.SHOW);
        boolean print = printPrograms;

        // determine the executable
        String exec = pickProverExec(proverToUse);
        if (exec == null || exec.trim().isEmpty()) {
            log.error("esc.no.exec", proverToUse); //$NON-NLS-1$
            return factory.makeProverResult(methodDecl.sym, proverToUse,
                    IProverResult.ERROR, null);
        }

        // create an SMT object, adding any options
        SMT smt = new SMT();
        smt.processCommandLine(new String[] {}, smt.smtConfig);
        Object o = JmlOption.value(context, JmlOption.TIMEOUT);
        if (o != null && !o.toString().isEmpty()) {
            try {
                smt.smtConfig.timeout = Double.parseDouble(o.toString());
            } catch (NumberFormatException e) {
                // FIXME - issue a warning
            }
        }

        // Add a listener for errors and start the solver.
        // The listener is set to use the defaultPrinter for printing
        // SMT abstractions and forwards all informational and error messages
        // to the OpenJML log mechanism
        smt.smtConfig.log.addListener(
                new SMTListener(log, smt.smtConfig.defaultPrinter));
        SMTTranslator smttrans = getTranslator(context,
                methodDecl.sym.toString());

        ISolver solver = null;

        Date start = new Date();
        setBenchmark(proverToUse, methodDecl.name.toString(), smt.smtConfig);
        solver = smt.startSolver(smt.smtConfig, proverToUse, exec);
        if (solver == null) {
            log.error("jml.solver.failed.to.start", exec);
            return factory.makeProverResult(methodDecl.sym, proverToUse,
                    IProverResult.ERROR, start);

        }

        IProverResult proofResult = null;

        try {

            solver.push(1); // Mark the top

            JCExpression converted = convertToImplication(p, q);

            // don't know
            if (converted == null) {
                return factory.makeProverResult(methodDecl.sym, proverToUse,
                        IProverResult.POSSIBLY_SAT, start);
            }
            IExpr script = smttrans.convertExpr(converted);

            
            if (printPrograms) {
                try {
                    log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                    log.getWriter(WriterKind.NOTICE).println(separator);
                    log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                    log.getWriter(WriterKind.NOTICE).println("SMT EQUVILANCE TRANSLATION OF " + utils.qualifiedMethodSig(methodDecl.sym));
                    org.smtlib.sexpr.Printer.WithLines.write(new PrintWriter(log.getWriter(WriterKind.NOTICE)),script);
                    log.getWriter(WriterKind.NOTICE).println();
                    log.getWriter(WriterKind.NOTICE).println();
                } catch (VisitorException e) {
                    log.getWriter(WriterKind.NOTICE).print("Exception while printing SMT script: " + e); 
                }
            }
            
            solver.assertExpr(script);

            IResponse solverResponse = solver.check_sat();

            utils.progress(1, 1,
                    "!(!context or q) <==> UNSAT for: " + converted.toString());

            IResponse unsatResponse = smt.smtConfig.responseFactory.unsat();

            utils.progress(1, 1,
                    "Checking Implication - " + q.toString() + " : "
                            + (solverResponse.equals(unsatResponse) ? "IMPLIES"
                                    : "DOES NOT IMPLY"));

            if (solverResponse.equals(unsatResponse)) {
                proofResult = factory.makeProverResult(methodDecl.sym,
                        proverToUse, IProverResult.UNSAT, start);
            } else if (solverResponse.isError()) {
                log.error("jml.esc.badscript", methodDecl.getName(),
                        smt.smtConfig.defaultPrinter.toString(solverResponse));
                proofResult = factory.makeProverResult(methodDecl.sym,
                        proverToUse, IProverResult.ERROR, start);
            } else {
                proofResult = factory.makeProverResult(methodDecl.sym,
                        proverToUse, IProverResult.POSSIBLY_SAT, start);
            }

        } finally {
            solver.exit();
            smt.smtConfig.logfile = null;
        }

        return proofResult;
    }

}
