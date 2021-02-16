/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.*;
import org.smtlib.ISort.IParameter;
import org.smtlib.impl.Command;
import org.smtlib.impl.SMTExpr.Symbol;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the define-sort command */
public class C_define_sort extends Command implements Idefine_sort {
	/** The command name */
	public static final String commandName = "define-sort";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	/** The name of the function being defined */
	protected ISymbol fcnName;
	/** The sorts of the arguments of the function being defined */
	protected List<IParameter> args;
	/** The defining expression for the function */
	protected ISort expression;
	
	/** The name of the function being defined */
	@Override
	public ISymbol sortSymbol() { return fcnName; }
	/** The sorts of the arguments of the function being defined */
	@Override
	public List<IParameter> parameters() { return args; };
	/** The defining expression for the function */
	@Override
	public ISort expression() { return expression; }
	
	/** Constructs a command instance */
	public C_define_sort(ISymbol id, List<IParameter> parameters, ISort expr) {
		this.fcnName = id;
		this.args = parameters;
		this.expression = expr;
	}
	
	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		sortSymbol().accept(p);
		p.writer().append(" (");
		for (IParameter d: parameters()) {
			d.accept(p);
			p.writer().append(" ");
		}
		p.writer().append(") ");
		expression().accept(p);
		p.writer().append(")");
	}
	
	/** Parses the command arguments and creates a command instance */
	static public /*@Nullable*/ C_define_sort parse(Parser p) throws ParserException {
		ISymbol name = p.parseSymbol();
		if (name == null) return null;
		if (p.parseLP() == null) return null;
		List<IParameter> list = new LinkedList<IParameter>();
		Set<Symbol> names = new HashSet<Symbol>();
		boolean anyErrors = false;
		while (!p.isRP()) {
			if (p.isEOD()) return null;
			Symbol d = p.parseSymbol();
			if (d == null) anyErrors = true;
			else {
				list.add(p.smt().sortFactory.createSortParameter(d));
				if (!names.add(d)) {
					error(p.smt(),"A name is duplicated in the parameter list: " + 
							p.smt().defaultPrinter.toString(d), d.pos());
					anyErrors = true;
				}
			}
		}
		p.parseRP();
		if (anyErrors) return null;
		ISort expr = p.parseSort(list);
		if (expr == null) return null;
		String v = name.value();
		if (v.length() > 0 && (v.charAt(0) == '@' || v.charAt(0) == '.')) {
			error(p.smt(),"User-defined symbols may not begin with . or @",name.pos());
			return null;
		}
		return new C_define_sort(name,list,expr);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.define_sort(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
	
	
}
