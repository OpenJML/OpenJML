/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iassert;
import org.smtlib.IExpr;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the assert command */
public class C_assert extends Command implements Iassert {
	
	/** Constructs a command object given the expression to assert */
	public C_assert(IExpr expr) {
		formula = expr;
	}
	
	/** Returns the asserted formula */
	@Override
	public IExpr expr() {
		return formula;
	}
	
	/** The command name */
	public static final String commandName = "assert";
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The formula to assert */
	protected IExpr formula;

	/** Writes out the command in S-expression syntax using the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		formula.accept(p);
		p.writer().append(")");
	}

	/** Parses the arguments of the command, producing a new command instance */
	static public /*@Nullable*/ C_assert parse(Parser p) throws IOException, ParserException {
		IExpr expr = p.parseExpr();
		if (expr == null) return null;
		return new C_assert(expr);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.assertExpr(formula);
	}
	
	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}


}
