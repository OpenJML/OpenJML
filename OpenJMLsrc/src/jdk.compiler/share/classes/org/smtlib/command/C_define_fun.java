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

import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.*;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the define-fun command */
public class C_define_fun extends Command implements Idefine_fun {
	/** The command name */
	public static final String commandName = "define-fun";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	/** The name of the function being defined */
	protected ISymbol fcnName;
	/** The sorts of the arguments of the function being defined */
	protected List<IDeclaration> args;
	/** The sort of the result */
	protected ISort resultSort;
	/** The defining expression for the function */
	protected IExpr expression;
	
	/** The name of the function being defined */
	@Override
	public ISymbol symbol() { return fcnName; }
	/** The sorts of the arguments of the function being defined */
	@Override
	public List<IDeclaration> parameters() { return args; };
	/** The result sort */
	@Override
	public ISort resultSort() { return resultSort; }
	/** The defining expression for the function */
	@Override
	public IExpr expression() { return expression; }
	
	// FIXME - typechecking needs to check that the resultSort matches the expression's sort
	
	/** Constructs a command instance */
	public C_define_fun(ISymbol id, List<IDeclaration> declarations, ISort resultSort, IExpr expr) {
		this.fcnName = id;
		this.args = declarations;
		this.resultSort = resultSort;
		this.expression = expr;
	}
	
	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		symbol().accept(p);
		p.writer().append(" (");
		for (IDeclaration d: parameters()) {
			d.accept(p);
		}
		p.writer().append(") ");
		resultSort().accept(p);
		p.writer().append(" ");
		expression().accept(p);
		p.writer().append(")");
	}
	
	/** Parses the command arguments and creates a command instance */
	static public /*@Nullable*/ C_define_fun parse(Parser p) throws ParserException {
		ISymbol name = p.parseSymbol();
		if (name == null) return null;
		if (p.parseLP() == null) return null;
		List<IDeclaration> list = new LinkedList<IDeclaration>();
		Set<ISymbol> names = new HashSet<ISymbol>();
		boolean anyErrors = false;
		while (!p.isRP()) {
			if (p.isEOD()) return null;
			IDeclaration d = p.parseDeclaration();
			if (d == null) anyErrors = true;
			else {
				list.add(d);
				if (!names.add(d.parameter())) {
					error(p.smt(),"A name is duplicated in the parameter list: " + 
							p.smt().defaultPrinter.toString(d.parameter()), d.parameter().pos());
					anyErrors = true;
				}
			}
		}
		p.parseRP();
		if (anyErrors) return null;
		ISort resultSort = p.parseSort(null);
		if (resultSort == null) return null;
		IExpr expr = p.parseExpr();
		if (expr == null) return null;
		String v = name.value();
		if (v.length() > 0 && (v.charAt(0) == '@' || v.charAt(0) == '.')) {
			error(p.smt(),"User-defined symbols may not begin with . or @",name.pos());
			return null;
		}
		return new C_define_fun(name,list,resultSort,expr);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.define_fun(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
