/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iexit;
import org.smtlib.IParser.ParserException;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the exit command */
public class C_echo extends Command implements Iexit {
	protected IStringLiteral arg;
	
	/** Constructs an instance of the command */
	public C_echo(IStringLiteral arg) {
		this.arg = arg;
	}
	
	/** Parses the arguments of the command, producing a new command instance */
	static public /*@Nullable*/ C_echo parse(Parser p) throws ParserException {
//		if (SMT.Configuration.isVersion(SMTLIB.V20)) {
//			p.error("The echo command is not valid in V2.0", p.peekToken().pos());
//			return null;
//		}
		IStringLiteral expr = p.parseStringLiteral();
		if (expr == null) return null;
		return new C_echo(expr);
	}

	public static final String commandName = "echo";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	@Override
	public IResponse execute(ISolver solver) {
		return solver.echo(arg);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
	
	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException {
		p.writer().append("(" + commandName + " " + arg + ")");  // FIXME Pretty printer for arg?
	}
	
}
