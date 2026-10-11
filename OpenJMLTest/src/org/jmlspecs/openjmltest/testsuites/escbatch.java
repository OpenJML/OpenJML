package org.jmlspecs.openjmltest.testsuites;

import java.io.File;

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
 * The first group runs some of the escfiles and escTimeLimits tests with --smt-batch; they use the
 * same source folders and expected output, since batching must not change any result, but write
 * their output to temp-escbatch, so this suite can run concurrently with those. The second group
 * runs SolverBatch directly on small scripts, against real solver processes. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escbatch extends EscBaseFiles {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }

    /** Runs ESC with --smt-batch on test/name, as helpEscName does, comparing with that folder's
     * expected output, which is first copied to temp-escbatch/name, where the output goes */
    void helpBatch(String name, String... opts) {
        String src = "test/" + name;
        String out = "temp-escbatch/" + name;
        try {
            new File(out).mkdirs();
            for (File f: new File(src).listFiles((d,n) -> n.startsWith("expected"))) {
                java.nio.file.Files.copy(f.toPath(), new File(out, f.getName()).toPath(),
                        java.nio.file.StandardCopyOption.REPLACE_EXISTING);
            }
        } catch (java.io.IOException e) {
            Assert.fail("Could not copy the expected output of " + src + ": " + e);
        }
        java.util.List<String> args = new java.util.ArrayList<>(java.util.List.of("-classpath", src,
                "--check-feasibility=precondition,reachable,exit,spec", "--spec-math=bigint"));
        args.addAll(java.util.List.of(opts));
        args.add("--smt-batch");
        helpEscFile(src, out, args.toArray(new String[0]));
    }

    // --- escfiles tests, with --smt-batch ---

    @Test
    public void escEnum() {
        helpBatch("escEnum");
    }

    @Test
    public void tuple() {
        helpBatch("tuple");
    }

    @Test
    public void escLoop() {
        helpBatch("escLoop");
    }

    @Test
    public void binarySearch() {
        helpBatch("binarySearch");
    }

    @Test // has a verification failure, so exercises the counterexample queries after a batch
    public void Dzmz() {
        helpBatch("Dzmz");
    }

    // --- escTimeLimits tests, with --smt-batch: batching does not change time-limit outcomes ---

    @Test
    public void gitbug1029m() {
        helpBatch("gitbug1029m", "--code-math=safe", "--check-feasibility=none", "--timeout=60", "--timeout-method=1");
    }

    @Test
    public void gitbug1029f() {
        helpBatch("gitbug1029f", "--code-math=safe", "--check-feasibility=all", "--timeout=60", "--timeout-method=10");
    }

    @Test
    public void gitbug1029r() {
        helpBatch("gitbug1029r", "--code-math=safe", "--check-feasibility=none", "--timeout=60", "--timeout-method=10");
    }

    // --- SolverBatch on small scripts ---

    static final String prelude =
        "(set-option :produce-models true)\n(set-logic ALL)\n";

    /** Starts the named solver from the solvers folder (SMT_SOLVER_DIR, set by runtests) */
    ISolver start(SMT smt, String solverName) {
        String exec = org.jmlspecs.openjml.Main.solvers + "/" + solverName;
        Assert.assertTrue("Solver not found: " + exec, new File(exec).exists());
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
        Assert.assertEquals("unsat", r[0]);
        Assert.assertEquals(r[0], r[1]);
    }

    @Test
    public void batchSameResultCvc5() throws Exception {
        String[] r = bothWays("cvc5-1.3.2", goodScript);
        Assert.assertEquals(r[0], r[1]);
    }

    static final String badScript = prelude
        + "(declare-fun x () Int)\n(assert (> x 0))\n(assert (> undeclared 0))\n(declare-fun z () Int)\n"
        + "(check-sat)\n";

    @Test // an error inside a block is reported, and z3 is still usable afterwards
    public void batchReportsErrorZ3() throws Exception {
        SMT smt = new SMT();
        ISolver solver = start(smt, "z3-5.1.0");
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
        try {
            IResponse r = SolverBatch.execute(parse(smt, badScript), solver);
            Assert.assertTrue("expected an error: " + r, r.isError());
        } finally {
            solver.exit();
        }
    }

    static final String hardQuery = prelude
        + "(declare-fun x () Int)\n(declare-fun y () Int)\n(declare-fun z () Int)\n"
        + "(assert (and (> x 0) (> y 0) (> z 0) (= (+ (* x x x) (* y y y)) (* z z z))))\n"
        + "(check-sat)\n";

    @Test(timeout = 60000) // a block sent after the solver's whole-run limit (--timeout-method) ended it gets the timeout response
    public void batchAfterTimeLimitZ3() throws Exception {
        SMT smt = new SMT();
        smt.smtConfig.timeoutTotal = 1;
        ISolver solver = start(smt, "z3-5.1.0");
        try {
            Assert.assertEquals("timeout", smt.smtConfig.defaultPrinter.toString(parse(smt, hardQuery).execute(solver)));
            IResponse r = SolverBatch.execute(parse(smt, "(declare-fun u () Int)\n(assert (> u 0))\n(check-sat)\n"), solver);
            Assert.assertEquals("timeout", smt.smtConfig.defaultPrinter.toString(r));
        } finally {
            solver.exit();
        }
    }
}
