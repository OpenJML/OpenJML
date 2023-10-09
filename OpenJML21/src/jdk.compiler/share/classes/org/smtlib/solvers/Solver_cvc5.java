/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import org.smtlib.*;

/** This class is an adapter that takes the SMT-LIB ASTs and translates them into SMT commands */
public class Solver_cvc5 extends Solver_cvc4 {
		
	/** Creates an instance of the solver */
	public Solver_cvc5(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
	    super(smtConfig, executable, "cvc5> ");
	}
	
}
