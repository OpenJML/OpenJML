/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Ipop;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the pop command */
public class C_pop extends Command implements Ipop {
	/** The command name */
	public static final String commandName = "pop";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	/** The (non-negative) number of stack frames to pop */
	//@ protected invariant n.value().compareTo(BigInteger.ZERO) > 0;
	protected INumeral numeral;
	
	/** The int value giving the number of stack frames to pop (set by check()), if the value is in the range of an int type */
	//@ protected invariant numeral.value().compareTo(BigInteger.MAX_INT) <= 0 ==> numeral.intValue() == number;
	protected int number;
	
	/** The number of assertion set stack items to pop */
	@Override
	public INumeral number() { 
		return numeral;
	}
	/** Constructs a command instance */
	//@ requires n.value().compareTo(BigInteger.ZERO) > 0;
	public C_pop(INumeral n) {
		numeral = n;
		number = n.intValue(); 
	}
	
	/** Parses the arguments of the command, producing a new command instance */
	static public /*@Nullable*/ C_pop parse(Parser p) throws ParserException {
		INumeral num = p.parseNumeral();
		if (num == null) return null;
		return new C_pop(num);
	}

	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		numeral.accept(p);
		p.writer().append(")");
	}
	
	@Override
	public IResponse execute(ISolver solver) {
		return solver.pop(number);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
