/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iset_logic;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** This class implements the set-logic command */
public class C_set_logic extends Command implements Iset_logic {

	/** The command name */
	public final static String commandName = "set-logic";
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The name of the logic to set */
	protected ISymbol logicName;
	
	/** The name of the logic to set */
	@Override
	public ISymbol logic() { return logicName; }

	public C_set_logic(ISymbol logic) {
		super();
		this.logicName = logic;
	}
	
	/** Creates a command instance by parsing the S-expression concrete syntax */
	static public C_set_logic parse(Parser p) throws ParserException {
		ISymbol logic = p.parseSymbol();
		if (logic == null) return null;
		return new C_set_logic(logic);
	}
	
	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		logicName.accept(p);
		p.writer().append(")");
	}

	@Override
	public IResponse execute(ISolver solver) {
		if (prefixText != null) solver.comment(prefixText);
		return solver.set_logic(logicName.value(),logicName.pos());
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
