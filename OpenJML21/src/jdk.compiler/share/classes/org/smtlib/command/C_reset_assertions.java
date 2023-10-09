/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iexit;
import org.smtlib.IParser.ParserException;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.SMT;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the reset-assertions command */
public class C_reset_assertions extends Command {
	/** Constructs an instance of the command */
	public C_reset_assertions() {
	}
	
	/** Parses the arguments of the command, producing a new command instance */
	static public /*@Nullable*/ C_reset_assertions parse(Parser p) throws ParserException {
//		if (SMT.Configuration.isVersion(SMTLIB.V20)) {
//			p.error("The reset-assertions command is not valid in V2.0", p.peekToken().pos());
//			return null;
//		}
		return p.checkNoArg() ? new C_reset_assertions() : null;
	}

	public static final String commandName = "reset-assertions";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	@Override
	public IResponse execute(ISolver solver) {
		return solver.reset_assertions();
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
	
	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException {
		p.writer().append("(" + commandName + ")");
	}
	
}
