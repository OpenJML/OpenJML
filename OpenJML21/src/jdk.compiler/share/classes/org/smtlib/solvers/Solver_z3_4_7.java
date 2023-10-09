package org.smtlib.solvers;

import org.smtlib.SMT;

public class Solver_z3_4_7  extends Solver_z3_4_5 {

    /** Creates an instance of the Z3 solver */
    public Solver_z3_4_7(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
        super(smtConfig,executable);
    }

    /** Creates an instance of the Z3 solver */
    public Solver_z3_4_7(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
        super(smtConfig,command);
    }
}
