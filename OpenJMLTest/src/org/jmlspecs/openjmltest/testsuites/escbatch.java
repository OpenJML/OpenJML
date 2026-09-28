package org.jmlspecs.openjmltest.testsuites;

import java.io.File;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.SolverBatch;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;
import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.SMT;

/** Tests of the --smt-batch option, which sends each run of SMT declarations and assertions
 * to the solver as one block with :print-success off (see SolverBatch).
 * <P>
 * The first group runs some of the escfiles tests with --smt-batch; they use the same test
 * folders and expected output as escfiles, since batching must not change any result. The
 * second group runs SolverBatch directly on small scripts, against real solver processes. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escbatch extends EscBaseFiles {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }

    // --- escfiles tests, with --smt-batch; expected output is shared with escfiles ---

    @Test
    public void escEnum() {
        helpEscName("escEnum", "--smt-batch");
    }

    @Test
    public void tuple() {
        helpEscName("tuple", "--smt-batch");
    }

    @Test
    public void escLoop() {
        helpEscName("escLoop", "--smt-batch");
    }

    @Test
    public void binarySearch() {
        helpEscName("binarySearch", "--smt-batch");
    }

    @Test // has a verification failure, so exercises the counterexample queries after a batch
    public void Dzmz() {
        helpEscName("Dzmz", "--smt-batch");
    }

    // --- SolverBatch on small scripts ---

    static final String prelude =
        "(set-option :produce-models true)\n(set-logic ALL)\n";

    /** Starts the named solver from the OpenJML solvers folder, or returns null if it is not installed */
    ISolver start(SMT smt, String solverName) {
        String exec = org.jmlspecs.openjml.Main.solvers + "/Solvers-" + Utils.identifyOS(null) + "/" + solverName;
        if (!new File(exec).exists()) return null;
        return smt.startSolver(smt.smtConfig, solverName, exec);
    }

    ICommand.IScript parse(SMT smt, String text) throws Exception {
        // parseScript expects the whole script in one pair of parentheses
        var source = smt.smtConfig.smtFactory.createSource("(" + text + ")", null);
        return smt.smtConfig.smtFactory.createParser(smt.smtConfig, source).parseScript();
    }

    /** Runs the script both ways (each on a fresh solver) and returns the two responses */
    String[] bothWays(String solverName, String text) throws Exception {
        String[] result = new String[2];
        for (int i = 0; i < 2; i++) {
            SMT smt = new SMT();
            ISolver solver = start(smt, solverName);
            if (solver == null) return null;
            try {
                ICommand.IScript script = parse(smt, text);
                IResponse r = i == 0 ? script.execute(solver) : SolverBatch.execute(script, solver);
                result[i] = smt.smtConfig.defaultPrinter.toString(r);
            } finally {
                solver.exit();
            }
        }
        return result;
    }

    static final String goodScript = prelude
        + "(declare-fun x () Int)\n(declare-fun y () Int)\n(declare-fun f (Int) Int)\n"
        + "(assert (forall ((i Int)) (! (> (f i) i) :pattern ((f i)))))\n"
        + "(assert (> x y))\n(assert (= y (f x)))\n"
        + "(push 1)\n(check-sat)\n";

    @Test
    public void batchSameResultZ3() throws Exception {
        String[] r = bothWays("z3-5.1.0", goodScript);
        org.junit.Assume.assumeNotNull((Object)r);
        Assert.assertEquals("unsat", r[0]);
        Assert.assertEquals(r[0], r[1]);
    }

    @Test
    public void batchSameResultCvc5() throws Exception {
        String[] r = bothWays("cvc5-1.3.2", goodScript);
        org.junit.Assume.assumeNotNull((Object)r);
        Assert.assertEquals(r[0], r[1]);
    }

    static final String badScript = prelude
        + "(declare-fun x () Int)\n(assert (> x 0))\n(assert (> undeclared 0))\n(declare-fun z () Int)\n"
        + "(check-sat)\n";

    @Test // an error inside a block is reported, and z3 is still usable afterwards
    public void batchReportsErrorZ3() throws Exception {
        SMT smt = new SMT();
        ISolver solver = start(smt, "z3-5.1.0");
        org.junit.Assume.assumeNotNull(solver);
        try {
            IResponse r = SolverBatch.execute(parse(smt, badScript), solver);
            Assert.assertTrue("expected an error: " + r, r.isError());
            Assert.assertTrue(smt.smtConfig.defaultPrinter.toString(r), smt.smtConfig.defaultPrinter.toString(r).contains("undeclared"));
            Assert.assertEquals("sat", smt.smtConfig.defaultPrinter.toString(solver.check_sat()));
        } finally {
            solver.exit();
        }
    }

    @Test(timeout = 60000) // cvc5 stops responding at an error; the batch must report it rather than wait for 'success'
    public void batchReportsErrorCvc5() throws Exception {
        SMT smt = new SMT();
        ISolver solver = start(smt, "cvc5-1.3.2");
        org.junit.Assume.assumeNotNull(solver);
        try {
            IResponse r = SolverBatch.execute(parse(smt, badScript), solver);
            Assert.assertTrue("expected an error: " + r, r.isError());
        } finally {
            solver.exit();
        }
    }
}
