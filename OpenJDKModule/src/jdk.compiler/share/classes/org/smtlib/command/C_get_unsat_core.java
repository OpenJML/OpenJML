/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iget_unsat_core;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the get-unsat-core command */
public class C_get_unsat_core extends Command implements Iget_unsat_core {
	/** Constructs a command instance */
	public C_get_unsat_core() {
	}
	
	/** Parses the command, producing a new command instance */
	static public /*@Nullable*/ C_get_unsat_core parse(Parser p) throws ParserException {
		return p.checkNoArg() ? new C_get_unsat_core() : null;
	}

	/** The command name */
	public static final String commandName = "get-unsat-core";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException {
		p.writer().append("(" + commandName + ")");
	}
	
	@Override
	public IResponse execute(ISolver solver) {
		return solver.get_unsat_core();
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
