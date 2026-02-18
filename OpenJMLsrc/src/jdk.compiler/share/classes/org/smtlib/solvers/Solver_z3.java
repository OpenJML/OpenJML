package org.smtlib.solvers;

import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.impl.Pos;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Solver_z3 extends Solver_z3_4_5 {
	protected String NAME_VALUE = "z3";

	/**
	 * Creates an instance of the Z3 solver
	 */
	public Solver_z3(final SMT.Configuration smtConfig, /*@NonNull*/ final String executable) {
		super(smtConfig, executable);
	}

	/**
	 * Creates an instance of the Z3 solver
	 */
	public Solver_z3(final SMT.Configuration smtConfig, /*@NonNull*/ final String[] command) {
		super(smtConfig, command);
	}
}
