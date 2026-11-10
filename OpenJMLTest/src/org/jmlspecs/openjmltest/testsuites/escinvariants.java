package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** ESC tests of invariants, in particular the 'invariants' method-spec clause (#651). Each test is a
 * directory under OpenJMLTest/test with the same name, compared against its 'expected' file.
 * The RAC counterpart is racfiles.invariantsClauseRac.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escinvariants extends EscBaseFiles {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }

    /** Parameter invariants are checked on normal exit, for the pre-state argument (#1104) */
    @Test
    public void gitbug1104() {
        helpEscSimple();
    }

    /** Type checking: clause placement and item kinds */
    @Test
    public void invariantsClause() {
        expectedExit = 1;
        helpEscSimple();
    }

    /** Entry, exit, call sites, constructors, inheritance */
    @Test
    public void invariantsClause2() {
        helpEscSimple();
    }

    /** At a call, items bind to the callee's arguments, not to same-named caller names */
    @Test
    public void invariantsClause3() {
        helpEscSimple();
    }

    /** Several specification cases; a reassigned parameter denotes its pre-state value at exit */
    @Test
    public void invariantsClause4() {
        helpEscSimple();
    }
}
