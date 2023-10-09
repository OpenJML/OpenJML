/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the declare-sort command */
public class C_declare_sort extends Command implements Ideclare_sort {
	/** The command name */
	public static final String commandName = "declare-sort";

	/** The new sort symbol */
	protected ISymbol sortSymbol;
	
	/** The arity of the sort symbol */
	protected INumeral arity;
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The arity of the sort symbol */
	@Override
	public INumeral arity() { return arity; }
	
	/** The sort symbol declared by this command */
	@Override
	public ISymbol sortSymbol() { return sortSymbol; }
	
	/** Constructs a new command object */
	public C_declare_sort(ISymbol id, INumeral n) {
		this.sortSymbol = id;
		this.arity = n;
	}
	
	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		sortSymbol.accept(p);
		p.writer().append(" ");
		arity.accept(p);
		p.writer().append(")");
	}

	/** Parses the arguments of the command, producing a new command instance */
	static public /*@Nullable*/C_declare_sort parse(Parser p) throws IOException, ParserException {
		/*@Nullable*/ISymbol id = p.parseSymbol();
		if (id == null) return null;
		/*@Nullable*/INumeral numeral = p.parseNumeral();
		if (numeral == null) return null;
		String v = id.value();
		if (v.length() > 0 && (v.charAt(0) == '@' || v.charAt(0) == '.')) {
			error(p.smt(),"User-defined symbols may not begin with . or @",id.pos());
			return null;
		}
		return new C_declare_sort(id,numeral);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.declare_sort(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
