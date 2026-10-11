package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** Tests whose expected outcome depends on a time limit: --timeout (each solver query) and --timeout-method (the
 * solver's total time for a method's proof), reached during the main proof, a feasibility check, or the search for
 * a further failure after a counterexample (#1029, #1022). Each test arranges for the query that should run into a
 * limit to be one the solver cannot decide (typically x^3 + y^3 == z^3 in positive integers), and for the limit that
 * should apply to be the small one, so the outcome does not depend on the machine's speed; where an easy query must
 * finish first, the limit leaves ample time for it even on a loaded machine.
 * <P>
 * Each test's source and expected output are in a folder of 'test' named like the test; the options are as for
 * escfiles3. (escTiming is a different suite: it measures how proofs scale with the number of branches.)
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escTimeLimits extends EscBaseFiles {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }

    public void helpEscSimple(String... opts) {
        addOptions("--code-math=safe");
        super.helpEscSimple(opts);
    }

    @Test
    public void gitbug1029() {
        // --timeout limits each solver query (#1029)
        helpEscSimple("--check-feasibility=none","--timeout=1");
    }

    @Test
    public void gitbug1029m() {
        // --timeout-method limits the solver's total time for a method's proof (#1029)
        helpEscSimple("--check-feasibility=none","--timeout=60","--timeout-method=1");
    }

    @Test
    public void gitbug1029f() {
        // --timeout-method also stops a method's feasibility checks (#1029)
        helpEscSimple("--check-feasibility=all","--timeout=60","--timeout-method=10");
    }

    @Test
    public void gitbug1029r() {
        // --timeout-method reached while looking for a further failure after a counterexample (#1029)
        helpEscSimple("--check-feasibility=none","--timeout=60","--timeout-method=10");
    }

    @Test
    public void gitbug1029rq() {
        // --timeout reached while looking for a further failure after a counterexample (#1029)
        helpEscSimple("--check-feasibility=none","--timeout=5");
    }

    @Test
    public void gitbug997b() {
        // Warnings: quantifiers with no term that can serve as a trigger; a feasibility check not decided
        // because of nonlinear arithmetic (the short timeout ends it quickly)
        helpEscSimple("--timeout=5","--check-feasibility=precondition");
    }

    @Test
    public void gitbug1001b() {
        // Loop invariants with \sum and \product that ESC does not yet prove (a short timeout keeps the
        // result 'Validity is unknown' on any machine)
        helpEscSimple("--timeout=10","--check-feasibility=none");
    }
}
