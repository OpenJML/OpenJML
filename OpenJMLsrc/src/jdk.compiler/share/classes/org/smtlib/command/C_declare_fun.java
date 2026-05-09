/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the declare-fun command */
public class C_declare_fun extends Command implements Ideclare_fun {
	
	/** The command name */
	public static final String commandName = "declare-fun";

	/** The name of the function being declared */
	protected ISymbol fcnName;

	/** The sorts of the arguments of the function being declared */
	protected List<ISort> argSorts;

	/** The result sort of the function being declared */
	protected ISort resultSort;
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	@Override
	public ISymbol symbol() { return fcnName; }
	
	@Override
	public List<ISort> argSorts() { return argSorts; }
	
	@Override
	public ISort resultSort() { return resultSort; }
	
	/** Constructs a command instance from its components */
	public C_declare_fun(ISymbol symbol, List<ISort> argSorts, ISort resultSort) {
		this.fcnName = symbol;
		this.argSorts = argSorts;
		this.resultSort = resultSort;
	}

	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		symbol().accept(p);
		p.writer().append(" (");
		for (ISort s: argSorts()) {
			s.accept(p);
			p.writer().append(" ");
		}
		p.writer().append(") ");
		resultSort().accept(p);
		p.writer().append(")");
		
	}

	/** Parses the arguments of the command, producing a new command instance */
	static public /*@Nullable*/ C_declare_fun parse(Parser p) throws ParserException {
		/*@Nullable*/ ISymbol symbol = p.parseSymbol();
		if (symbol == null) return null;
		List<ISort> argSorts = new LinkedList<ISort>();
		boolean anyErrors = false;
		if (p.parseLP() == null) return null;
		while (!p.isRP()) {
			if (p.isEOD()) return null;
			ISort s = p.parseSort(null);
			if (s == null) anyErrors = true;
			else argSorts.add(s);
		}
		p.parseRP();
		if (anyErrors) return null;

		/*@Nullable*/ ISort result = p.parseSort(null);
		if (result == null) return null;
		String v = symbol.value();
		if (v.length() > 0 && (v.charAt(0) == '@' || v.charAt(0) == '.')) {
			error(p.smt(),"User-defined symbols may not begin with . or @",symbol.pos());
			return null;
		}
		return new C_declare_fun(symbol,argSorts,result);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.declare_fun(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
