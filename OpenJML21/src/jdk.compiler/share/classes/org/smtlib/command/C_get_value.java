/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.smtlib.ICommand.Iget_value;
import org.smtlib.IExpr;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.ILexToken;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the get-value command */
public class C_get_value extends Command implements Iget_value {

	/** The command name */
	public static final String commandName = "get-value";
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The terms whose values are to be gotten */
	protected List<IExpr> terms;
	
	/** The terms whose values are to be gotten */
	@Override
	public List<IExpr> exprs() { return terms; }
	
	/** Constructs a command instance */
	public C_get_value(List<IExpr> terms) {
		this.terms = terms;
	}
	
	/** Parses the command, producing a new command instance */
	static public /*@Nullable*/ C_get_value parse(Parser p) throws ParserException {
		List<IExpr> list = new LinkedList<IExpr>();
		boolean anyErrors = false;
		if (!p.isLP()) {
			error(p.smt(),"Expected a parenthesized list of terms beginning here",
					p.pos(p.currentPos()-1,p.currentPos()));
			return null;
		}
		ILexToken lp = p.parseLP();
		while (!p.isRP() && !p.isEOD()) {
			IExpr e = p.parseExpr();
			if (e == null) anyErrors = true;
			else list.add(e);
		}
		ILexToken rp = p.parseRP();
		if (anyErrors) { return null; }
		if (list.isEmpty()) {
			error(p.smt(),"Expected a parenthesized list of at least one term",
					p.pos(lp.pos().charStart(),rp.pos().charEnd()));
			return null;
		}
		return new C_get_value(list);
	}

	
	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " (");
		for (IExpr e: exprs()) {
			p.writer().append(" ");
			e.accept(p);
		}
		p.writer().append("))");
	}
	
	@Override
	public IResponse execute(ISolver solver) {
		return solver.get_value(exprs().toArray(new IExpr[exprs().size()]));
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
