/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iget_option;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the get-option command */
public class C_get_option extends Command implements Iget_option {
	/** The command name */
	public static final String commandName = "get-option";
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The keyword for the option to fetch */
	protected IKeyword option;
	
	/** The keyword for the option to fetch */
	@Override
	public IKeyword option() {
		return option;
	}
	
	/** Constructs a command instance for the given keyword */
	public C_get_option(IKeyword keyword) { 
		super();
		this.option = keyword;
	}
	
	/** Creates a command instance by parsing the concrete S-expression syntax */
	static public /*@Nullable*/C_get_option parse(Parser p) throws ParserException {
		IKeyword key = p.parseKeyword();
		if (key == null) return null;
		return new C_get_option(key);
	}
	
	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		option.accept(p);
		p.writer().append(")");
	}

	@Override
	public IResponse execute(ISolver solver) {
		if (prefixText != null) solver.comment(prefixText);
		return solver.get_option(option);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
