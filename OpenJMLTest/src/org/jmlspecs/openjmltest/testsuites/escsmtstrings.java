package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** \string operations in ESC, with the SMT-LIB Strings theory (--smt-strings) and with the array model
 * (--no-smt-strings) (#1043). The tests run the sources in test/smtstrings; each has its own expected output. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escsmtstrings extends EscBaseFiles {

    /** Methods that z3 does not settle within the time limit in one of the modes: with the Strings theory,
     * the character indexing of built strings (Chars) and the laws of the order together (Order.properties);
     * with the array model, Equalities.literals. smtstringsCvc5 checks the Chars methods with cvc5. */
    static final String EXCLUDED = "--exclude=Chars.build,Chars.shifted,Chars.substrings,Chars.unchanged,Order.properties,Equalities.literals";

    void helpStrings(String outDir, String... opts) {
        String d = "test/smtstrings";
        String[] firstopts = { "-classpath", d, "--check-feasibility=none", "--spec-math=bigint", "--timeout=60" };
        String[] newopts = new String[firstopts.length + opts.length];
        System.arraycopy(firstopts, 0, newopts, 0, firstopts.length);
        System.arraycopy(opts, 0, newopts, firstopts.length, opts.length);
        helpEscFile(d, "test/" + outDir, newopts);
    }

    @Test
    public void smtstrings() {
        helpStrings("smtstrings", "--smt-strings", EXCLUDED);
    }

    @Test
    public void smtstringsArray() {
        helpStrings("smtstringsArray", "--no-smt-strings", EXCLUDED);
    }

    @Test
    public void smtstringsCvc5() {
        // cvc5 settles quickly the character facts about built strings that z3 does not (with the Strings theory)
        helpStrings("smtstringsCvc5", "--smt-strings", "--prover=cvc5-1.3.2",
                "--method=Chars.build,Chars.shifted,Chars.substrings,Chars.unchanged,Equalities.literals,Equalities.split");
    }
}
