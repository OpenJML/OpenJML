/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration;

/**
 *  This is a special handler for Z3 4.3.2, as opposed to other revisions of Z3 4.3.
 *  
 *  @see Solver_z3_4_3
 */
public class Solver_z3_4_3_2 extends Solver_z3_4_3 {
	
    protected String NAME_VALUE = "z3-4.3.2";
    protected String AUTHORS_VALUE = "Leonardo de Moura and Nikolaj Bjorner";
    protected String VERSION_VALUE = "4.3.2";

	public Solver_z3_4_3_2(Configuration smtConfig, String executable) {
		super(smtConfig, executable);
	}
	
	@Override
	public IResponse push(int number) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a push command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A push command called with a negative argument: " + number);
		checkSatStatus = null;
		if (number == 0) return smtConfig.responseFactory.success();
		try {
			pushesDepth += number;
			// This odd invocation is to correct a bug in Z3 4.3.2, where (push) can print out more than one success message.
			solverProcess.sendNoListen("(push ",Integer.toString(number),")\n");
			solverProcess.sendNoListen("(echo \"<<DONE>>\")\n");
			String s;
			do {
				s = solverProcess.listen();
			} while (!s.contains("<<DONE>>"));
			// FIXME: If an error occurs, this will loop forever.
			// We can't use parseResponse to see if it an error, as the function does not expect Z3's buggy output.
			return successOrEmpty(smtConfig);
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}
}
