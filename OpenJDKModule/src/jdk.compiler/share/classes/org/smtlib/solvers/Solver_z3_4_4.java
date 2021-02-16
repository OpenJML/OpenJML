/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import org.smtlib.SMT.Configuration;


/** This class is an adapter that takes the SMT-LIB ASTs and translates them into Z3 commands.
 * 
 *  @see Solver_z3_4_3
 */
public class Solver_z3_4_4 extends Solver_z3_4_3_2 {
    
    protected String NAME_VALUE = "z3-4.4";
    protected String AUTHORS_VALUE = "Leonardo de Moura and Nikolaj Bjorner";
    protected String VERSION_VALUE = "4.4";

	protected String cmds_win[] = new String[]{ "", "/smt2","/in"};
	protected String cmds_mac[] = new String[]{ "", "-smt2","-in","SMTLIB2_COMPLIANT=true"}; 
	protected String cmds_unix[] = new String[]{ "", "-smt2","-in"}; 

    public Solver_z3_4_4(Configuration smtConfig, String executable) {
        super(smtConfig, executable);
    }
}
